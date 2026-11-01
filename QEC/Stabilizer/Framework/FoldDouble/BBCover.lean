import QEC.Stabilizer.Framework.Homological.BBDoubling
import QEC.Stabilizer.Framework.Homological.Distance
import QEC.Stabilizer.Framework.FoldDouble.Distance

/-!
# Fold and double for a free double cover of a bivariate-bicycle code

A free double cover `D : XDoubleCoverData G H` of bivariate-bicycle codes pairs
the cover qubits `G × Fin 2` by the deck translation: each qubit `q` with its
partner `deckSigma1 q`, the pair being indexed by the base qubit
`Prod.map proj id q`, with the section `sec1` picking sheet `0`. This file
spells out the dictionary between that pairing and the chain-level transfer
maps of `BBCover.lean`:

* `D.pairing : Fin n ≃ Fin m × Fin 2` is the pairing on the qubit indices of
  the cover code, with the base qubit indices as the pairs;
* on X-type (and Z-type) chain operators, the sheets are `D.sheet0`/`D.sheet1`,
  the fold is the pushforward `D.push1`, the double is the pullback
  `D.pull1`, and the sheet swap is the deck shift `D.deckShift1`
  (`fold_chainXOperator`, `double_chainXOperator`, …);
* the pairing is symmetric for the cover's CSS stabilizer group
  (`isSymmetric_pairing`), because boundaries and dual boundaries are
  translation invariant;
* the tight witness of the doubling theorem is a doubling logical of the
  general theory (`isDoublingLogical_chainXOperator_of_witness`): hypothesis
  (W);
* the deck homotopy `DeckTrivialOnH1` gives condition (R) for *every* logical
  operator of the cover code, X-type, Z-type or mixed
  (`condition_R_of_deckTrivialOnH1`): the Z side follows from the X side
  through the duality involution `bbDualFn`, which commutes with the deck
  shift;
* `DangerousFloorNZ (2 d)` gives condition (S) for the X-type logical
  operators (`condition_S_of_dangerousFloorNZ`), and `SeamCosetFloor (2 d)`
  gives condition (F) for the X-type seam logicals
  (`condition_F_of_seamCosetFloor`).

## What remains to recover `pauli_distance_eq_double_of_admissible`

Conditions (F) and (S) of `isLeast_logicalWeight_two_mul_of_symmetric`
quantify over *all* seam logicals and *all* nontrivial logical operators,
whatever their Pauli type, while the inputs of the doubling theorem of
`BBDoubling.lean` only control the X sector: its Z sector is handled by the
duality `bb_cycle_bound_iff_dual_bound`, and mixed operators by the CSS
bridge `chainWeight_lower_bound_transfers`. The X-sector statements proved
here are exactly the dangerous and safe floors of that development, so the
missing piece is a sector version of Theorem 5.1 for CSS codes (hypotheses
on the X-type operators only, conclusion on the X-type logicals), after which
the Z sector follows by duality and the mixed operators by the CSS bridge as
in `pauli_distance_eq_double_of_logicalFloor`.
-/

namespace Quantum
namespace Stabilizer

open NQubitPauliOperator NQubitPauliGroupElement StabilizerGroup

/-! ## Chain operators of a homological code, read on qubits -/

namespace Homological
namespace HomologicalCode

variable {X : HomologicalCode}

/-- The X-type chain operator of `c` at the qubit of the edge `q`. -/
lemma chainXOperator_operators_edgeEquiv (c : X.C1 → ZMod 2) (q : X.C1) :
    (X.chainXOperator c).operators (X.edgeEquiv q) =
      if c q = 1 then PauliOperator.X else PauliOperator.I := by
  simp only [chainXOperator_op_at, Equiv.apply_eq_iff_eq, exists_eq_left]

/-- The Z-type chain operator of `c` at the qubit of the edge `q`. -/
lemma chainZOperator_operators_edgeEquiv (c : X.C1 → ZMod 2) (q : X.C1) :
    (X.chainZOperator c).operators (X.edgeEquiv q) =
      if c q = 1 then PauliOperator.Z else PauliOperator.I := by
  simp only [chainZOperator_op_at, Equiv.apply_eq_iff_eq, exists_eq_left]

/-- The operator part of any Pauli element is the product of the X-type chain
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

/-- Every element of the X-closure has the operator part of the X-type chain
operator of a boundary. -/
lemma exists_mem_boundaries_of_mem_closure_XGenerators
    {x : NQubitPauliGroupElement X.numQubits} (hx : x ∈ Subgroup.closure X.XGenerators) :
    ∃ c ∈ X.boundaries, x.operators = (X.chainXOperator c).operators := by
  refine Subgroup.closure_induction
    (p := fun y _ => ∃ c ∈ X.boundaries, y.operators = (X.chainXOperator c).operators)
    ?_ ?_ ?_ ?_ hx
  · rintro y ⟨f, rfl⟩
    exact ⟨X.boundary2 (X.singleFace f), ⟨X.singleFace f, rfl⟩, rfl⟩
  · exact ⟨0, X.boundaries.zero_mem, by rw [chainXOperator_zero]⟩
  · rintro y₁ y₂ _ _ ⟨c₁, hc₁, h₁⟩ ⟨c₂, hc₂, h₂⟩
    exact ⟨c₁ + c₂, X.boundaries.add_mem hc₁ hc₂,
      by rw [chainXOperator_add, mul_operators, mul_operators, h₁, h₂]⟩
  · rintro y _ ⟨c, hc, h⟩
    exact ⟨c, hc, by rw [inv_operators, h]⟩

/-- Every element of the Z-closure has the operator part of the Z-type chain
operator of a dual boundary. -/
lemma exists_mem_dualBoundaries_of_mem_closure_ZGenerators
    {z : NQubitPauliGroupElement X.numQubits} (hz : z ∈ Subgroup.closure X.ZGenerators) :
    ∃ c ∈ X.dualBoundaries, z.operators = (X.chainZOperator c).operators := by
  refine Subgroup.closure_induction
    (p := fun y _ => ∃ c ∈ X.dualBoundaries, y.operators = (X.chainZOperator c).operators)
    ?_ ?_ ?_ ?_ hz
  · rintro y ⟨v, rfl⟩
    exact ⟨X.cutMap (X.singleVtx v), ⟨X.singleVtx v, rfl⟩, rfl⟩
  · exact ⟨0, X.dualBoundaries.zero_mem, by rw [chainZOperator_zero]⟩
  · rintro y₁ y₂ _ _ ⟨c₁, hc₁, h₁⟩ ⟨c₂, hc₂, h₂⟩
    exact ⟨c₁ + c₂, X.dualBoundaries.add_mem hc₁ hc₂,
      by rw [chainZOperator_add, mul_operators, mul_operators, h₁, h₂]⟩
  · rintro y _ ⟨c, hc, h⟩
    exact ⟨c, hc, by rw [inv_operators, h]⟩

/-- CSS decomposition of a stabilizer element on operator parts: a Z-type chain
operator of a dual boundary times an X-type chain operator of a boundary. -/
lemma exists_operators_eq_of_mem_homologicalStabilizerGroup
    {s : NQubitPauliGroupElement X.numQubits} (hs : s ∈ X.homologicalStabilizerGroup.toSubgroup) :
    ∃ cz ∈ X.dualBoundaries, ∃ cx ∈ X.boundaries,
      s.operators = (X.chainZOperator cz).operators * (X.chainXOperator cx).operators := by
  obtain ⟨z, hz, x, hx, rfl⟩ :=
    Subgroup.mem_closure_union_exists_mul_of_commute_generators ZGenerators_commute_XGenerators s hs
  obtain ⟨cz, hcz, hz'⟩ := exists_mem_dualBoundaries_of_mem_closure_ZGenerators hz
  obtain ⟨cx, hcx, hx'⟩ := exists_mem_boundaries_of_mem_closure_XGenerators hx
  exact ⟨cz, hcz, cx, hcx, by rw [mul_operators, hz', hx']⟩

end HomologicalCode
end Homological

namespace Homological
namespace BB
namespace XDoubleCoverData

open HomologicalCode FoldDouble

variable {G H : Type}
  [Fintype G] [AddCommGroup G] [DecidableEq G]
  [Fintype H] [AddCommGroup H] [DecidableEq H]
  (D : XDoubleCoverData G H)

/-! ## The pairing induced by the deck translation -/

/-- The pairing of the cover qubits `G × Fin 2` by the deck translation: a
qubit is sent to its base qubit together with its sheet, sheet `0` being the
image of the section. -/
def coverPairing : (G × Fin 2) ≃ (H × Fin 2) × Fin 2 where
  toFun q := ((D.proj q.1, q.2), if q.1 = D.sec (D.proj q.1) then 0 else 1)
  invFun x := (if x.2 = 0 then D.sec x.1.1 else D.sec x.1.1 + D.deckS, x.1.2)
  left_inv := by
    rintro ⟨g, i⟩
    change (if (if g = D.sec (D.proj g) then (0 : Fin 2) else 1) = 0 then D.sec (D.proj g)
      else D.sec (D.proj g) + D.deckS, i) = (g, i)
    by_cases hg : g = D.sec (D.proj g)
    · rw [if_pos hg, if_pos rfl, ← hg]
    · have hg' : g = D.sec (D.proj g) + D.deckS := (D.point_dichotomy g).resolve_left hg
      rw [if_neg hg, if_neg (by decide), ← hg']
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
lemma coverPairing_symm_flip (q : G × Fin 2) :
    D.coverPairing.symm ((D.coverPairing q).1, Fin.rev (D.coverPairing q).2) =
      D.deckSigma1 q := by
  obtain ⟨g, i⟩ := q
  by_cases hg : g = D.sec (D.proj g)
  · have h2 : (D.coverPairing (g, i)).2 = 0 := if_pos hg
    rw [h2, rev_zero_two, coverPairing_apply_fst, coverPairing_symm_one]
    simp only [XDoubleCoverData.sec1, XDoubleCoverData.deckSigma1, Prod.map_apply, id]
    rw [← hg]
  · have hg' : g = D.sec (D.proj g) + D.deckS := (D.point_dichotomy g).resolve_left hg
    have h2 : (D.coverPairing (g, i)).2 = 1 := if_neg hg
    rw [h2, rev_one_two, coverPairing_apply_fst, coverPairing_symm_zero]
    simp only [XDoubleCoverData.sec1, XDoubleCoverData.deckSigma1, Prod.map_apply, id]
    conv_rhs => rw [hg']
    rw [add_assoc, D.deckS_add_deckS, add_zero]

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
      D.coverComplex.edgeEquiv (D.coverPairing.symm (p, s)) := by
  rw [pairing, Equiv.symm_trans_apply, Equiv.symm_trans_apply, Equiv.symm_symm]
  change D.coverComplex.edgeEquiv (D.coverPairing.symm
    (D.baseComplex.edgeEquiv.symm (D.baseComplex.edgeEquiv p), s)) = _
  rw [Equiv.symm_apply_apply]

lemma pairing_symm_zero (p : H × Fin 2) :
    D.pairing.symm (D.baseComplex.edgeEquiv p, 0) = D.coverComplex.edgeEquiv (D.sec1 p) := by
  rw [pairing_symm_apply, coverPairing_symm_zero]

lemma pairing_symm_one (p : H × Fin 2) :
    D.pairing.symm (D.baseComplex.edgeEquiv p, 1) =
      D.coverComplex.edgeEquiv (D.deckSigma1 (D.sec1 p)) := by
  rw [pairing_symm_apply, coverPairing_symm_one]

lemma pairing_fst (q : G × Fin 2) :
    (D.pairing (D.coverComplex.edgeEquiv q)).1 =
      D.baseComplex.edgeEquiv (Prod.map D.proj id q) := by
  rw [pairing_apply]
  rfl

/-- The partner of a cover qubit under the pairing is its deck partner. -/
lemma partner_pairing (q : G × Fin 2) :
    partner D.pairing (D.coverComplex.edgeEquiv q) = D.coverComplex.edgeEquiv (D.deckSigma1 q) := by
  simp only [partner, pairing_apply, pairing_symm_apply, coverPairing_symm_flip]

/-! ## The dictionary on X-type and Z-type chain operators -/

section Dictionary

variable (v : G × Fin 2 → ZMod 2) (u : H × Fin 2 → ZMod 2)

lemma sheet_zero_chainXOperator :
    sheet D.pairing 0 (D.coverComplex.chainXOperator v).operators =
      (D.baseComplex.chainXOperator (D.sheet0 v)).operators := by
  apply NQubitPauliOperator.ext
  intro j
  obtain ⟨p, rfl⟩ := D.baseComplex.edgeEquiv.surjective j
  rw [sheet_apply, pairing_symm_zero, chainXOperator_operators_edgeEquiv,
    chainXOperator_operators_edgeEquiv]
  rfl

lemma sheet_one_chainXOperator :
    sheet D.pairing 1 (D.coverComplex.chainXOperator v).operators =
      (D.baseComplex.chainXOperator (D.sheet1 v)).operators := by
  apply NQubitPauliOperator.ext
  intro j
  obtain ⟨p, rfl⟩ := D.baseComplex.edgeEquiv.surjective j
  rw [sheet_apply, pairing_symm_one, chainXOperator_operators_edgeEquiv,
    chainXOperator_operators_edgeEquiv]
  rfl

/-- The fold of an X-type chain operator is the X-type chain operator of the
pushforward. -/
theorem fold_chainXOperator :
    fold D.pairing (D.coverComplex.chainXOperator v).operators =
      (D.baseComplex.chainXOperator (D.push1 v)).operators := by
  rw [fold, sheet_zero_chainXOperator, sheet_one_chainXOperator, ← mul_operators,
    ← chainXOperator_add]
  exact congrArg (fun c => (D.baseComplex.chainXOperator c).operators)
    (funext (D.sheet0_add_sheet1 v))

/-- The double of an X-type chain operator is the X-type chain operator of the
pullback. -/
theorem double_chainXOperator :
    double D.pairing (D.baseComplex.chainXOperator u).operators =
      (D.coverComplex.chainXOperator (D.pull1 u)).operators := by
  apply NQubitPauliOperator.ext
  intro i
  obtain ⟨q, rfl⟩ := D.coverComplex.edgeEquiv.surjective i
  rw [double_apply, pairing_fst, chainXOperator_operators_edgeEquiv,
    chainXOperator_operators_edgeEquiv]
  rfl

/-- The sheet swap of an X-type chain operator is the X-type chain operator of
the deck shift. -/
theorem sheetSwap_chainXOperator :
    sheetSwap D.pairing (D.coverComplex.chainXOperator v).operators =
      (D.coverComplex.chainXOperator (D.deckShift1 v)).operators := by
  apply NQubitPauliOperator.ext
  intro i
  obtain ⟨q, rfl⟩ := D.coverComplex.edgeEquiv.surjective i
  rw [sheetSwap_apply, partner_pairing, chainXOperator_operators_edgeEquiv,
    chainXOperator_operators_edgeEquiv]
  rfl

lemma sheet_zero_chainZOperator :
    sheet D.pairing 0 (D.coverComplex.chainZOperator v).operators =
      (D.baseComplex.chainZOperator (D.sheet0 v)).operators := by
  apply NQubitPauliOperator.ext
  intro j
  obtain ⟨p, rfl⟩ := D.baseComplex.edgeEquiv.surjective j
  rw [sheet_apply, pairing_symm_zero, chainZOperator_operators_edgeEquiv,
    chainZOperator_operators_edgeEquiv]
  rfl

lemma sheet_one_chainZOperator :
    sheet D.pairing 1 (D.coverComplex.chainZOperator v).operators =
      (D.baseComplex.chainZOperator (D.sheet1 v)).operators := by
  apply NQubitPauliOperator.ext
  intro j
  obtain ⟨p, rfl⟩ := D.baseComplex.edgeEquiv.surjective j
  rw [sheet_apply, pairing_symm_one, chainZOperator_operators_edgeEquiv,
    chainZOperator_operators_edgeEquiv]
  rfl

/-- The fold of a Z-type chain operator is the Z-type chain operator of the
pushforward. -/
theorem fold_chainZOperator :
    fold D.pairing (D.coverComplex.chainZOperator v).operators =
      (D.baseComplex.chainZOperator (D.push1 v)).operators := by
  rw [fold, sheet_zero_chainZOperator, sheet_one_chainZOperator, ← mul_operators,
    ← chainZOperator_add]
  exact congrArg (fun c => (D.baseComplex.chainZOperator c).operators)
    (funext (D.sheet0_add_sheet1 v))

/-- The double of a Z-type chain operator is the Z-type chain operator of the
pullback. -/
theorem double_chainZOperator :
    double D.pairing (D.baseComplex.chainZOperator u).operators =
      (D.coverComplex.chainZOperator (D.pull1 u)).operators := by
  apply NQubitPauliOperator.ext
  intro i
  obtain ⟨q, rfl⟩ := D.coverComplex.edgeEquiv.surjective i
  rw [double_apply, pairing_fst, chainZOperator_operators_edgeEquiv,
    chainZOperator_operators_edgeEquiv]
  rfl

/-- The sheet swap of a Z-type chain operator is the Z-type chain operator of
the deck shift. -/
theorem sheetSwap_chainZOperator :
    sheetSwap D.pairing (D.coverComplex.chainZOperator v).operators =
      (D.coverComplex.chainZOperator (D.deckShift1 v)).operators := by
  apply NQubitPauliOperator.ext
  intro i
  obtain ⟨q, rfl⟩ := D.coverComplex.edgeEquiv.surjective i
  rw [sheetSwap_apply, partner_pairing, chainZOperator_operators_edgeEquiv,
    chainZOperator_operators_edgeEquiv]
  rfl

end Dictionary

/-! ## Translation invariance of boundaries and dual boundaries -/

/-- Boundaries of the cover complex are invariant under the deck shift. -/
lemma deckShift1_mem_boundaries {c : G × Fin 2 → ZMod 2}
    (hc : c ∈ D.coverComplex.boundaries) : D.deckShift1 c ∈ D.coverComplex.boundaries := by
  obtain ⟨f, rfl⟩ := hc
  exact ⟨D.deckShift0 f, bbBoundary2Fn_translate D.Ac D.Bc D.deckS f⟩

/-- The duality involution commutes with the deck shift. -/
lemma bbDualFn_deckShift1 (c : G × Fin 2 → ZMod 2) :
    bbDualFn (D.deckShift1 c) = D.deckShift1 (bbDualFn c) := by
  funext p
  obtain ⟨g, j⟩ := p
  fin_cases j <;>
    simp [bbDualFn, deckShift1, blockSwapNeg, D.neg_deckS, add_comm]

/-- Dual boundaries of the cover complex are invariant under the deck shift. -/
lemma deckShift1_mem_dualBoundaries {c : G × Fin 2 → ZMod 2}
    (hc : c ∈ D.coverComplex.dualBoundaries) :
    D.deckShift1 c ∈ D.coverComplex.dualBoundaries := by
  have h1 : bbDualFn c ∈ D.coverComplex.boundaries := by
    have := (bbDual_mem_dualBoundaries_iff D.Ac D.Bc (bbDualFn c)).mp
    rw [bbDualFn_bbDualFn] at this
    exact this hc
  have h2 := D.deckShift1_mem_boundaries h1
  rw [← D.bbDualFn_deckShift1] at h2
  have h3 := (bbDual_mem_dualBoundaries_iff D.Ac D.Bc (bbDualFn (D.deckShift1 c))).mpr h2
  rwa [bbDualFn_bbDualFn] at h3

/-- The deck acts trivially on the dual homology too: the dual of the deck
homotopy, through the duality involution. -/
theorem deckTrivialOnH1_dual (hR : D.DeckTrivialOnH1) :
    ∀ c : G × Fin 2 → ZMod 2, c ∈ D.coverComplex.dualCycles →
      c + D.deckShift1 c ∈ D.coverComplex.dualBoundaries := by
  intro c hc
  have h1 : bbDualFn c ∈ D.coverComplex.cycles := by
    have := (bbDual_mem_dualCycles_iff D.Ac D.Bc (bbDualFn c)).mp
    rw [bbDualFn_bbDualFn] at this
    exact this hc
  have h2 := hR _ h1
  have h3 : bbDualFn (c + D.deckShift1 c) = bbDualFn c + D.deckShift1 (bbDualFn c) := by
    rw [← D.bbDualFn_deckShift1]
    rfl
  rw [← h3] at h2
  have h4 := (bbDual_mem_dualBoundaries_iff D.Ac D.Bc (bbDualFn (c + D.deckShift1 c))).mpr h2
  rwa [bbDualFn_bbDualFn] at h4

/-! ## The hypotheses of the symmetric theorem for the cover code -/

/-- The pairing by the deck translation is symmetric for the cover code. -/
theorem isSymmetric_pairing :
    IsSymmetric D.pairing D.coverComplex.homologicalStabilizerGroup := by
  intro s hs
  obtain ⟨cz, hcz, cx, hcx, hops⟩ := exists_operators_eq_of_mem_homologicalStabilizerGroup hs
  rw [hops, sheetSwap_mul, sheetSwap_chainZOperator, sheetSwap_chainXOperator]
  refine (operatorImage _).mul_mem (operators_mem_operatorImage ?_)
    (operators_mem_operatorImage ?_)
  · exact Subgroup.closure_mono Set.subset_union_left
      ((chainZOperator_mem_ZClosure_iff_mem_dualBoundaries _).mpr
        (D.deckShift1_mem_dualBoundaries hcz))
  · exact Subgroup.closure_mono Set.subset_union_right
      ((chainXOperator_mem_XClosure_iff_mem_boundaries _).mpr
        (D.deckShift1_mem_boundaries hcx))

/-- Hypothesis (W): the tight witness of the doubling theorem — a base cycle
whose pullback is not a cover boundary — is a doubling logical of the general
theory. -/
theorem isDoublingLogical_chainXOperator_of_witness (uStar : H × Fin 2 → ZMod 2)
    (hu_cyc : uStar ∈ D.baseComplex.cycles) (hτnb : D.pull1 uStar ∉ D.coverComplex.boundaries) :
    IsDoublingLogical D.pairing D.coverComplex.homologicalStabilizerGroup
      (D.baseComplex.chainXOperator uStar).operators := by
  have hnt := (chainXOperator_isNontrivialLogical_iff (X := D.coverComplex) (D.pull1 uStar)).mpr
    ⟨D.pull1_mem_cycles hu_cyc, hτnb⟩
  rw [isNontrivialLogicalOperator_iff_operators, mem_centralizer_iff_operators_mem] at hnt
  rw [IsDoublingLogical, mem_doublingGroup, mem_seamGroup, double_chainXOperator]
  exact hnt

/-- The weight of the witness, as an element of the phase-free Pauli group, is
its chain weight. -/
lemma weight_chainXOperator_operators (u : H × Fin 2 → ZMod 2) :
    weight (D.baseComplex.chainXOperator u).operators = D.baseComplex.chainWeight u :=
  weight_chainXOperator (X := D.baseComplex) u

/-- Hypothesis (R): the deck homotopy on `H₁` gives `g * g^σ ∈ G` for every
logical operator `g` of the cover code, of any Pauli type. -/
theorem condition_R_of_deckTrivialOnH1 (hR : D.DeckTrivialOnH1) :
    ∀ g ∈ centralizer D.coverComplex.homologicalStabilizerGroup,
      g.operators * sheetSwap D.pairing g.operators ∈
        operatorImage D.coverComplex.homologicalStabilizerGroup.toSubgroup := by
  intro g hg
  rw [operators_eq_chainXOperator_mul_chainZOperator g, sheetSwap_mul, sheetSwap_chainXOperator,
    sheetSwap_chainZOperator, mul_mul_mul_comm, ← mul_operators, ← chainXOperator_add,
    ← mul_operators, ← chainZOperator_add]
  refine (operatorImage _).mul_mem (operators_mem_operatorImage ?_)
    (operators_mem_operatorImage ?_)
  · exact Subgroup.closure_mono Set.subset_union_right
      ((chainXOperator_mem_XClosure_iff_mem_boundaries _).mpr
        (hR _ (xChainOf_mem_cycles_of_centralizer g hg)))
  · exact Subgroup.closure_mono Set.subset_union_left
      ((chainZOperator_mem_ZClosure_iff_mem_dualBoundaries _).mpr
        (D.deckTrivialOnH1_dual hR _ (zChainOf_mem_dualCycles_of_centralizer g hg)))

/-- Hypothesis (R) in the form of Proposition 3.4 (4): `P ≤ T`. -/
theorem logicalFoldImage_le_seamGroup_of_deckTrivialOnH1 (hR : D.DeckTrivialOnH1) :
    logicalFoldImage D.pairing D.coverComplex.homologicalStabilizerGroup ≤
      seamGroup D.pairing D.coverComplex.homologicalStabilizerGroup :=
  (logicalFoldImage_le_seamGroup_iff _ _).mp (D.condition_R_of_deckTrivialOnH1 hR)

/-! ## The X-sector forms of (S) and (F) -/

lemma push1_eq_of_fold_eq {c : G × Fin 2 → ZMod 2}
    {s : NQubitPauliGroupElement D.coverComplex.numQubits}
    (hs : s ∈ D.coverComplex.homologicalStabilizerGroup.toSubgroup)
    (h : fold D.pairing s.operators = (D.baseComplex.chainXOperator (D.push1 c)).operators) :
    D.push1 c ∈ D.baseComplex.boundaries := by
  obtain ⟨cz, hcz, cx, hcx, hops⟩ := exists_operators_eq_of_mem_homologicalStabilizerGroup hs
  rw [hops, fold_mul, fold_chainZOperator, fold_chainXOperator] at h
  have hkey : ∀ a b c : ZMod 2,
      ((if a = 1 then PauliOperator.Z else PauliOperator.I).mulOp
        (if b = 1 then PauliOperator.X else PauliOperator.I)).operator =
        (if c = 1 then PauliOperator.X else PauliOperator.I) → b = c := by decide
  have heq : D.push1 cx = D.push1 c := by
    funext p
    have hp := congrFun h (D.baseComplex.edgeEquiv p)
    rw [NQubitPauliOperator.mul_apply, chainZOperator_operators_edgeEquiv,
      chainXOperator_operators_edgeEquiv, chainXOperator_operators_edgeEquiv] at hp
    exact hkey _ _ _ hp
  rw [← heq]
  exact D.push1_mem_boundaries hcx

/-- Hypothesis (S) for the X-type logical operators: `DangerousFloorNZ (2d)`
gives `wt b + 2 · (residual weight of v) ≥ 2d` for every X-type nontrivial
logical `v` folding to a stabilizer fold `b ≠ 1`. -/
theorem condition_S_of_dangerousFloorNZ {d : ℕ} (hM : D.DangerousFloorNZ (2 * d)) :
    ∀ b ∈ foldImage D.pairing D.coverComplex.homologicalStabilizerGroup, b ≠ 1 →
      ∀ c : G × Fin 2 → ZMod 2,
        IsNontrivialLogicalOperator (D.coverComplex.chainXOperator c)
          D.coverComplex.homologicalStabilizerGroup →
        fold D.pairing (D.coverComplex.chainXOperator c).operators = b →
        2 * d ≤ weight b + 2 * residualWeight D.pairing (D.coverComplex.chainXOperator c) := by
  intro b hbJ hb1 c hc hcb
  rw [chainXOperator_isNontrivialLogical_iff] at hc
  obtain ⟨s, hs, hsb⟩ := (mem_foldImage _ _).mp hbJ
  rw [fold_chainXOperator] at hcb
  have hpush : D.push1 c ∈ D.baseComplex.boundaries :=
    D.push1_eq_of_fold_eq hs (hsb.trans hcb.symm)
  have hne : D.push1 c ≠ 0 := by
    intro h0
    apply hb1
    rw [← hcb, h0]
    exact congrArg NQubitPauliGroupElement.operators chainXOperator_zero
  have hw := hM c hc.1 hc.2 hpush hne
  have hslice := weight_eq_weight_fold_add_two_mul_weight_outsideSupport D.pairing
    (D.coverComplex.chainXOperator c).operators
    (Or.inl (chainXOperator_isXType (X := D.coverComplex) c).2)
  unfold residualWeight
  rw [fold_chainXOperator, hcb] at hslice ⊢
  rw [← hslice, ← weight_eq_weight_operators, weight_chainXOperator]
  exact hw

/-- Sheet `1` of a pullback is the base chain. -/
lemma sheet1_pull1 (u : H × Fin 2 → ZMod 2) : D.sheet1 (D.pull1 u) = u := by
  funext q
  change u (Prod.map ⇑D.proj id (D.deckSigma1 (D.sec1 q))) = u q
  obtain ⟨p, i⟩ := q
  simp [XDoubleCoverData.deckSigma1, XDoubleCoverData.sec1, D.proj_add_deckS, D.proj_sec]

/-- Hypothesis (F) for the X-type seam logicals: `SeamCosetFloor (2d)` gives
weight `≥ 2d` to every X-type seam logical. -/
theorem condition_F_of_seamCosetFloor {d : ℕ} (hMim : D.SeamCosetFloor (2 * d)) :
    ∀ ζ : H × Fin 2 → ZMod 2,
      IsSeamLogical D.pairing D.coverComplex.homologicalStabilizerGroup
        (D.baseComplex.chainXOperator ζ).operators →
      2 * d ≤ weight (D.baseComplex.chainXOperator ζ).operators := by
  rintro ζ ⟨hT, hJ⟩
  rw [mem_seamGroup, double_chainXOperator] at hT
  obtain ⟨s, hs, hsops⟩ := mem_operatorImage.mp hT
  have hpull : D.pull1 ζ ∈ D.coverComplex.boundaries :=
    stabilizer_same_ops_implies_boundary _ s hs hsops
  have hnb : ζ ∉ D.baseComplex.boundaries := by
    rintro ⟨f, rfl⟩
    apply hJ
    refine (mem_foldImage _ _).mpr ⟨D.coverComplex.chainXOperator (D.liftStab f), ?_, ?_⟩
    · exact Subgroup.closure_mono Set.subset_union_right
        ((chainXOperator_mem_XClosure_iff_mem_boundaries _).mpr (D.liftStab_mem_boundaries f))
    · rw [fold_chainXOperator, D.push1_liftStab]
      rfl
  obtain ⟨z, hz⟩ := hpull
  have hz' : bbBoundary2Fn D.Ac D.Bc z = D.pull1 ζ := hz
  set ξ₀ := D.sheetC2_0 z with hξ₀
  set ξ₁ := D.sheetC2_1 z with hξ₁
  have hsplit : D.pull1 ζ = D.liftStab ξ₀ + D.deckShift1 (D.liftStab ξ₁) := by
    rw [← hz']
    conv_lhs => rw [D.liftC2_decomp z]
    rw [bbBoundary2Fn_add, D.liftStab_deckShift]
    rfl
  have h0 : ∀ j, ζ j = D.seamN ξ₀ j + D.seamC ξ₁ j := by
    intro j
    calc ζ j = D.sheet0 (D.pull1 ζ) j := by rw [D.sheet0_pull1]
      _ = D.sheet0 (D.liftStab ξ₀ + D.deckShift1 (D.liftStab ξ₁)) j := by rw [hsplit]
      _ = D.seamN ξ₀ j + D.seamC ξ₁ j := by
          rw [D.sheet0_add, Pi.add_apply, D.sheet0_deckShift1]
          rfl
  have h1 : ∀ j, ζ j = D.seamC ξ₀ j + D.seamN ξ₁ j := by
    intro j
    calc ζ j = D.sheet1 (D.pull1 ζ) j := by rw [D.sheet1_pull1]
      _ = D.sheet1 (D.liftStab ξ₀ + D.deckShift1 (D.liftStab ξ₁)) j := by rw [hsplit]
      _ = D.seamC ξ₀ j + D.seamN ξ₁ j := by
          rw [D.sheet1_add, Pi.add_apply, D.sheet1_deckShift1]
          rfl
  have hker : bbBoundary2Fn D.Ab D.Bb (ξ₀ + ξ₁) = 0 := by
    funext j
    rw [bbBoundary2Fn_add, Pi.add_apply, Pi.zero_apply]
    have hkey : ∀ n0 c0 n1 c1 w b0 b1 : ZMod 2,
        w = n0 + c1 → w = c0 + n1 → n0 + c0 = b0 → n1 + c1 = b1 → b0 + b1 = 0 := by decide
    exact hkey _ _ _ _ _ _ _ (h0 j) (h1 j) (D.seamN_add_seamC ξ₀ j) (D.seamN_add_seamC ξ₁ j)
  have hform : ζ = D.seamC (ξ₀ + ξ₁) + bbBoundary2Fn D.Ab D.Bb ξ₀ := by
    funext j
    rw [Pi.add_apply, D.seamC_add, Pi.add_apply]
    have hkey : ∀ n0 c0 c1 w b0 : ZMod 2,
        w = n0 + c1 → n0 + c0 = b0 → w = (c0 + c1) + b0 := by decide
    exact hkey _ _ _ _ _ (h0 j) (D.seamN_add_seamC ξ₀ j)
  have hm : 2 * d ≤ D.baseComplex.chainWeight ζ := by
    rw [hform]
    refine hMim _ hker _ ?_
    rw [← hform]
    exact hnb
  rw [weight_chainXOperator_operators]
  exact hm

end XDoubleCoverData
end BB
end Homological
end Stabilizer
end Quantum
