import QEC.Stabilizer.Framework.Concatenation.Promotion

/-!
# Concatenation, Tier 1b: the `concatenate` constructor

Milestone **M3** of the CSS concatenation plan
(`pipeline/attempts/concat_css_general/plan.md`).

Assembles the M1 embedding calculus and the M2 promotion/generator-list into a
bona-fide `StabilizerCode (n₁ * n₂) k₂` from a `ConcatCSSData`. The conceptual
crux is `promote_anticommute_parity` (plan risk **R6**): two promoted outer
generators commute *on the nose* because promotion preserves the parity of the
anticommuting-position count, and the underlying outer generators commute.

**Status: M3 skeleton.** The structural plumbing typechecks; the obligation
proofs are tagged `sorry`s (`concat-m3`). They are the focused next step:
- `promote_anticommute_parity` (R6) — the parity core, to build/verify first.
- `concat_generators_commute` — 4-case dispatch (inner/inner, inner/promoted,
  promoted/promoted) built on R6, M1's `embedBlock_*`, and the inner logicals
  being in `Cin`'s centralizer.
- `concat_closure_no_neg_identity` — regroup the generator set as `Z ∪ X` (via
  `inner_split`/`outer_split`) and apply `negIdentity_not_mem_closure_union`.
- `concat_generators_independent` — block-structured check-matrix independence
  via the symplectic span bridge (or, fallback, a `ConcatCSSData` field).
- the concat logicals' centralizer membership + anticommutation.
-/

namespace Quantum.Concatenation

open NQubitPauliGroupElement StabilizerGroup

variable {n₁ n₂ k₂ : ℕ} [NeZero n₁]

namespace ConcatCSSData

variable (D : ConcatCSSData n₁ n₂ k₂)

/-! ## R6 foundations: the inner logicals as zero-phase operators -/

/-- `ofOperator Xbar` is the inner logical `X` (they agree because `X̄` has phase 0). -/
lemma ofOperator_Xbar : ofOperator D.Xbar = (D.Cin.logicalOps 0).xOp := by
  apply NQubitPauliGroupElement.ext
  · rw [ofOperator_phasePower, D.innerLogX_phaseZero]
  · rfl

/-- `ofOperator Zbar` is the inner logical `Z`. -/
lemma ofOperator_Zbar : ofOperator D.Zbar = (D.Cin.logicalOps 0).zOp := by
  apply NQubitPauliGroupElement.ext
  · rw [ofOperator_phasePower, D.innerLogZ_phaseZero]
  · rfl

/-- The promotion targets `X̄`, `Z̄` anticommute (they are the inner logical pair). -/
lemma Xbar_Zbar_anticommute : Anticommute (ofOperator D.Xbar) (ofOperator D.Zbar) := by
  rw [D.ofOperator_Xbar, D.ofOperator_Zbar]; exact (D.Cin.logicalOps 0).anticommute

/-- A Pauli operator never anticommutes with itself at any position. -/
lemma not_anticommutesAt_self {m : ℕ} (A : NQubitPauliOperator m) (i : Fin m) :
    ¬ anticommutesAt A A i := by
  intro h
  rw [NQubitPauliGroupElement.anticommutesAt] at h
  have hv := congrArg Fin.val h
  simp only [Fin.val_add] at hv
  omega

/-- Per-position reduction: two promoted operators anticommute at physical qubit `q`
exactly when the single-qubit promotions of `h₁`,`h₂` at block `blockOf q` anticommute
at the in-block position `posOf q`. -/
lemma anticommutesAt_promoteE (h₁ h₂ : NQubitPauliGroupElement n₂) (q : Fin (n₁ * n₂)) :
    anticommutesAt (promoteE D.Xbar D.Zbar h₁).operators (promoteE D.Xbar D.Zbar h₂).operators q
      = anticommutesAt (promoteSingle D.Xbar D.Zbar (h₁.operators (blockOf q)))
          (promoteSingle D.Xbar D.Zbar (h₂.operators (blockOf q))) (posOf q) := by
  simp only [NQubitPauliGroupElement.anticommutesAt, promoteE_operators, promoteOp]

/-! ## Commutation obligation (R6 parity core) -/

open Classical in
/-- Block-decomposition: the promoted anticommuting-position count is the sum over
blocks of the per-block single-qubit promoted counts. -/
lemma promote_count_eq_sum (h₁ h₂ : NQubitPauliGroupElement n₂) :
    (Finset.univ.filter (anticommutesAt (promoteE D.Xbar D.Zbar h₁).operators
        (promoteE D.Xbar D.Zbar h₂).operators)).card
      = ∑ b : Fin n₂, (Finset.univ.filter (anticommutesAt
          (promoteSingle D.Xbar D.Zbar (h₁.operators b))
          (promoteSingle D.Xbar D.Zbar (h₂.operators b)))).card := by
  rw [Finset.card_eq_sum_card_fiberwise (fun q _ => Finset.mem_univ (blockOf q))]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.filter_filter]
  have himg : Finset.univ.filter (fun q => anticommutesAt (promoteE D.Xbar D.Zbar h₁).operators
        (promoteE D.Xbar D.Zbar h₂).operators q ∧ blockOf q = b)
      = (Finset.univ.filter (anticommutesAt (promoteSingle D.Xbar D.Zbar (h₁.operators b))
          (promoteSingle D.Xbar D.Zbar (h₂.operators b)))).image (qIdx b) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hac, hb⟩
      refine ⟨posOf q, ?_, by rw [← hb]; exact qIdx_blockOf_posOf q⟩
      rw [D.anticommutesAt_promoteE, hb] at hac
      exact hac
    · rintro ⟨i, hi, rfl⟩
      refine ⟨?_, blockOf_qIdx b i⟩
      rw [D.anticommutesAt_promoteE, blockOf_qIdx, posOf_qIdx]
      exact hi
  rw [himg, Finset.card_image_of_injective _ (fun i i' h => (qIdx_injective h).2)]

open Classical in
/-- Per-block parity: the single-qubit promoted count at block `b` is odd iff the
underlying outer operators anticommute at `b` (requires no-`Y` at `b`). -/
lemma cnt_odd_iff (h₁ h₂ : NQubitPauliGroupElement n₂) (b : Fin n₂)
    (hY₁ : h₁.operators b ≠ PauliOperator.Y) (hY₂ : h₂.operators b ≠ PauliOperator.Y) :
    Odd (Finset.univ.filter (anticommutesAt (promoteSingle D.Xbar D.Zbar (h₁.operators b))
        (promoteSingle D.Xbar D.Zbar (h₂.operators b)))).card
      ↔ anticommutesAt h₁.operators h₂.operators b := by
  sorry
  -- TODO(concat-m3,R6): the MATH is settled and the case structure is correct —
  -- `rcases` on (h₁ b, h₂ b) ∈ {I,X,Z}² (Y excluded by hY); the 2 off-diagonal cases
  -- (X,Z)/(Z,X) are odd via `anticommutes_iff_odd_anticommutes` + `Xbar_Zbar_anticommute`
  -- (+`anticommute_symm`); the 7 commuting cases have an empty filter (card 0) via
  -- `not_anticommutesAt_self` / `not_anticommutesAt_of_{left,right}_I`; `decide` then
  -- closes each concrete iff (it reduces the noncomputable `mulOp` through the rfl table).
  -- BLOCKER: closing the 7 even cases requires reducing `(filter (anticommutesAt A B) univ).card`
  -- to 0, but the goal's `DecidablePred` instance on that filter won't unify with any
  -- constructed `card = 0` / `filter = ∅` / `sum_eq_zero` term (rw/simp metavars don't pin
  -- to the goal's instance). Needs an instance-alignment fix (e.g. `Finset.filter_congr_decidable`,
  -- a `classical`-uniform restatement, or a `Finset.card_filter`-sum form proven by `Finset.sum_congr`).

open Classical in
/-- **(R6)** Promotion preserves the parity of the anticommuting-position count:
the count of physical qubits where two promoted outer operators anticommute has the
same parity as the count of outer qubits where the underlying operators anticommute.
This is exactly why promoted outer generators commute on the nose.

The `no-Y` hypotheses are essential: `promoteSingle` sends `Y ↦ I`, which would break
the per-block parity at any `Y`. CSS outer generators (Z-type or X-type) satisfy them.

Foundations in place (`ofOperator_Xbar/Zbar`, `Xbar_Zbar_anticommute`,
`not_anticommutesAt_self`, `anticommutesAt_promoteE`). Remaining: block-decompose the
LHS count (`card_eq_sum_card_fiberwise` by `blockOf`, per-fiber bijection via `qIdx`);
per-block parity (`Odd cnt_b ↔ anticommutesAt h₁ h₂ b`) by `{I,X,Z}²` case analysis
using `anticommutes_iff_odd_anticommutes` + `Xbar_Zbar_anticommute` + the two falsity
lemmas; then mod-2 assembly via `Finset.card_filter` + `Finset.sum_nat_mod`. -/
lemma promote_anticommute_parity (h₁ h₂ : NQubitPauliGroupElement n₂)
    (hY₁ : ∀ b, h₁.operators b ≠ PauliOperator.Y)
    (hY₂ : ∀ b, h₂.operators b ≠ PauliOperator.Y) :
    Even (Finset.univ.filter (anticommutesAt (promoteE D.Xbar D.Zbar h₁).operators
        (promoteE D.Xbar D.Zbar h₂).operators)).card
      ↔ Even (Finset.univ.filter (anticommutesAt h₁.operators h₂.operators)).card := by
  sorry -- TODO(concat-m3,R6): block-decomp + per-block parity + mod-2 assembly (see docstring).

/-- All concatenated generators pairwise commute. -/
lemma concat_generators_commute :
    ∀ g ∈ listToSet D.concatGeneratorsList,
      ∀ h ∈ listToSet D.concatGeneratorsList, g * h = h * g := by
  sorry -- TODO(concat-m3): 4-case dispatch. inner/inner: embedBlock_commute_iff /
  -- embedBlock_cross_commute + Cin.generators_commute. inner/promoted: inner logicals are
  -- in Cin's centralizer ⇒ embedded stab commutes with promoted block op. promoted/promoted:
  -- commutes_iff_even_anticommutes + promote_anticommute_parity + Cout.generators_commute.

/-! ## No `-I`, independence -/

/-- The closure of the concatenated generators omits `-I`. -/
lemma concat_closure_no_neg_identity :
    negIdentity (n₁ * n₂) ∉ Subgroup.closure (listToSet D.concatGeneratorsList) := by
  sorry -- TODO(concat-m3): regroup listToSet concatGeneratorsList = Zset ∪ Xset
  -- (embedded innerZ + promoted outerZ, resp. innerX/outerX) via inner_split/outer_split,
  -- typed by promoteE_isZ/isX + embedBlock typing; apply negIdentity_not_mem_closure_union.

/-- The concatenated generator list is independent. -/
lemma concat_generators_independent :
    GeneratorsIndependent (n₁ * n₂) D.concatGeneratorsList := by
  sorry -- TODO(concat-m3): GeneratorsIndependent_of_rowsLinearIndependent; block-structured
  -- check matrix: per-block inner rows (disjoint supports) ⊕ promoted-outer rows separated by
  -- not_mem_subgroup_of_symp_not_in_span. (Fallback: accept as a ConcatCSSData field.)

/-! ## The stabilizer group and the logical operators -/

/-- The stabilizer group of the concatenated code. -/
noncomputable def concatStabGroup : StabilizerGroup (n₁ * n₂) :=
  mkStabilizerFromGenerators (n₁ * n₂) D.concatGeneratorsList
    (concat_generators_commute D) (concat_closure_no_neg_identity D)

/-- Concatenated logical `X` for logical qubit `ℓ`: the promoted outer logical `X`. -/
def concatLogicalX (ℓ : Fin k₂) : NQubitPauliGroupElement (n₁ * n₂) :=
  promoteE D.Xbar D.Zbar (D.Cout.logicalOps ℓ).xOp

/-- Concatenated logical `Z` for logical qubit `ℓ`: the promoted outer logical `Z`. -/
def concatLogicalZ (ℓ : Fin k₂) : NQubitPauliGroupElement (n₁ * n₂) :=
  promoteE D.Xbar D.Zbar (D.Cout.logicalOps ℓ).zOp

lemma concatLogicalX_mem_centralizer (ℓ : Fin k₂) :
    concatLogicalX D ℓ ∈ centralizer (concatStabGroup D) := by
  sorry -- TODO(concat-m3): commutes with each generator; inner stabs via X̄ ∈ Cin centralizer,
  -- promoted outer via promote_anticommute_parity + (Cout.logicalOps ℓ).xOp in Cout centralizer.

lemma concatLogicalZ_mem_centralizer (ℓ : Fin k₂) :
    concatLogicalZ D ℓ ∈ centralizer (concatStabGroup D) := by
  sorry -- TODO(concat-m3): symmetric to concatLogicalX_mem_centralizer.

lemma concatLogical_anticommute (ℓ : Fin k₂) :
    Anticommute (concatLogicalX D ℓ) (concatLogicalZ D ℓ) := by
  sorry -- TODO(concat-m3): odd-parity side from (Cout.logicalOps ℓ).anticommute via R6

/-- The bundled logical operators of the concatenated code. -/
def concatLogicalOps (ℓ : Fin k₂) : LogicalQubitOps (n₁ * n₂) (concatStabGroup D) where
  xOp := concatLogicalX D ℓ
  zOp := concatLogicalZ D ℓ
  x_mem_centralizer := concatLogicalX_mem_centralizer D ℓ
  z_mem_centralizer := concatLogicalZ_mem_centralizer D ℓ
  anticommute := concatLogical_anticommute D ℓ

lemma concat_logical_commute_cross (ℓ ℓ' : Fin k₂) (hne : ℓ ≠ ℓ') :
    (concatLogicalOps D ℓ).xOp * (concatLogicalOps D ℓ').xOp =
        (concatLogicalOps D ℓ').xOp * (concatLogicalOps D ℓ).xOp ∧
      (concatLogicalOps D ℓ).xOp * (concatLogicalOps D ℓ').zOp =
        (concatLogicalOps D ℓ').zOp * (concatLogicalOps D ℓ).xOp ∧
      (concatLogicalOps D ℓ).zOp * (concatLogicalOps D ℓ').xOp =
        (concatLogicalOps D ℓ').xOp * (concatLogicalOps D ℓ).zOp ∧
      (concatLogicalOps D ℓ).zOp * (concatLogicalOps D ℓ').zOp =
        (concatLogicalOps D ℓ').zOp * (concatLogicalOps D ℓ).zOp := by
  sorry -- TODO(concat-m3): promote_anticommute_parity + Cout.logical_commute_cross ℓ ℓ' hne.

/-! ## The constructor -/

/-- Concatenate a `k₁ = 1` CSS inner code with a CSS outer code into a
`StabilizerCode (n₁ * n₂) k₂`. The headline of M3. -/
noncomputable def concatenate (D : ConcatCSSData n₁ n₂ k₂) : StabilizerCode (n₁ * n₂) k₂ where
  hk := by
    have hk := D.Cout.hk
    have hle : n₂ ≤ n₁ * n₂ := Nat.le_mul_of_pos_left n₂ (Nat.pos_of_ne_zero (NeZero.ne n₁))
    omega
  generatorsList := D.concatGeneratorsList
  generators_length := D.concatGeneratorsList_length
  generators_phaseZero := D.concatGeneratorsList_phaseZero
  generators_independent := concat_generators_independent D
  generators_commute := concat_generators_commute D
  closure_no_neg_identity := concat_closure_no_neg_identity D
  logicalOps := concatLogicalOps D
  logical_commute_cross := concat_logical_commute_cross D

end ConcatCSSData

end Quantum.Concatenation
