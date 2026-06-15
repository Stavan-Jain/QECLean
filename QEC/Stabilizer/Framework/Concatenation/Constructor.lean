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

/-- `1 ≠ -1` in the `n`-qubit Pauli group (distinct phase powers). -/
lemma one_ne_minusOne {n : ℕ} : (1 : NQubitPauliGroupElement n) ≠ minusOne n := by
  intro he
  have := congrArg NQubitPauliGroupElement.phasePower he
  simp at this

/-- An element never anticommutes with itself (it would force `1 = -1`). -/
lemma not_anticommute_self {n : ℕ} (p : NQubitPauliGroupElement n) : ¬ Anticommute p p := by
  intro h
  rw [Anticommute] at h
  exact one_ne_minusOne (mul_right_cancel (b := p * p) (by rw [one_mul]; exact h))

/-- The identity never anticommutes with anything on the left. -/
lemma not_anticommute_one_left {n : ℕ} (g : NQubitPauliGroupElement n) : ¬ Anticommute 1 g := by
  intro h
  rw [Anticommute, one_mul, mul_one] at h
  exact one_ne_minusOne (mul_right_cancel (b := g) (by rw [one_mul]; exact h))

/-- The identity never anticommutes with anything on the right. -/
lemma not_anticommute_one_right {n : ℕ} (g : NQubitPauliGroupElement n) : ¬ Anticommute g 1 :=
  fun h => not_anticommute_one_left g (anticommute_symm _ _ h)

/-- The zero-phase embedding of the identity operator is the group identity. -/
@[simp] lemma ofOperator_identity {n : ℕ} :
    ofOperator (NQubitPauliOperator.identity n) = 1 := rfl

open Classical in
/-- Per-block parity: the single-qubit promoted count at block `b` is odd iff the
underlying outer operators anticommute at `b` (requires no-`Y` at `b`).

Proved filter-free: convert `Odd (filter …).card` to `Anticommute (ofOperator …)` via
`anticommutes_iff_odd_anticommutes`, then a `{I,X,Z}²` case analysis using the group-level
`Anticommute` facts (self / `1` / `X̄·Z̄`). This sidesteps the `DecidablePred` instance
mismatch that blocks any `card = 0` rewrite on the goal's filter. -/
lemma cnt_odd_iff (h₁ h₂ : NQubitPauliGroupElement n₂) (b : Fin n₂)
    (hY₁ : h₁.operators b ≠ PauliOperator.Y) (hY₂ : h₂.operators b ≠ PauliOperator.Y) :
    Odd (Finset.univ.filter (anticommutesAt (promoteSingle D.Xbar D.Zbar (h₁.operators b))
        (promoteSingle D.Xbar D.Zbar (h₂.operators b)))).card
      ↔ anticommutesAt h₁.operators h₂.operators b := by
  have hodd : Odd (Finset.univ.filter (anticommutesAt
        (promoteSingle D.Xbar D.Zbar (h₁.operators b))
        (promoteSingle D.Xbar D.Zbar (h₂.operators b)))).card
      ↔ Anticommute (ofOperator (promoteSingle D.Xbar D.Zbar (h₁.operators b)))
          (ofOperator (promoteSingle D.Xbar D.Zbar (h₂.operators b))) :=
    (anticommutes_iff_odd_anticommutes
      (ofOperator (promoteSingle D.Xbar D.Zbar (h₁.operators b)))
      (ofOperator (promoteSingle D.Xbar D.Zbar (h₂.operators b)))).symm
  rw [hodd]
  rcases hP : h₁.operators b with _ | _ | _ | _ <;>
      rcases hQ : h₂.operators b with _ | _ | _ | _ <;>
      first
        | exact absurd hP hY₁
        | exact absurd hQ hY₂
        | (conv_rhs => unfold NQubitPauliGroupElement.anticommutesAt
           simp only [hP, hQ, promoteSingle, ofOperator_identity]
           first
             | exact iff_of_true D.Xbar_Zbar_anticommute (by decide)
             | exact iff_of_true (anticommute_symm _ _ D.Xbar_Zbar_anticommute) (by decide)
             | exact iff_of_false (not_anticommute_self _) (by decide)
             | exact iff_of_false (not_anticommute_one_left _) (by decide)
             | exact iff_of_false (not_anticommute_one_right _) (by decide))

open Classical in
/-- **(R6)** Promotion preserves the parity of the anticommuting-position count:
the count of physical qubits where two promoted outer operators anticommute has the
same parity as the count of outer qubits where the underlying operators anticommute.
This is exactly why promoted outer generators commute on the nose.

The `no-Y` hypotheses are essential: `promoteSingle` sends `Y ↦ I`, which would break
the per-block parity at any `Y`. CSS outer generators (Z-type or X-type) satisfy them.

Proof: block-decompose the promoted count (`promote_count_eq_sum`), reduce mod 2 to a
sum of per-block parities (`cnt_odd_iff`), and match against the outer count written as
`∑ indicators` (`Finset.card_filter`). -/
lemma promote_anticommute_parity (h₁ h₂ : NQubitPauliGroupElement n₂)
    (hY₁ : ∀ b, h₁.operators b ≠ PauliOperator.Y)
    (hY₂ : ∀ b, h₂.operators b ≠ PauliOperator.Y) :
    Even (Finset.univ.filter (anticommutesAt (promoteE D.Xbar D.Zbar h₁).operators
        (promoteE D.Xbar D.Zbar h₂).operators)).card
      ↔ Even (Finset.univ.filter (anticommutesAt h₁.operators h₂.operators)).card := by
  have key : (Finset.univ.filter (anticommutesAt (promoteE D.Xbar D.Zbar h₁).operators
        (promoteE D.Xbar D.Zbar h₂).operators)).card % 2
      = (Finset.univ.filter (anticommutesAt h₁.operators h₂.operators)).card % 2 := by
    rw [D.promote_count_eq_sum h₁ h₂, Finset.card_filter, Finset.sum_nat_mod]
    congr 1
    refine Finset.sum_congr rfl (fun b _ => ?_)
    by_cases hb : anticommutesAt h₁.operators h₂.operators b
    · simp only [if_pos hb]
      exact Nat.odd_iff.mp ((D.cnt_odd_iff h₁ h₂ b (hY₁ b) (hY₂ b)).mpr hb)
    · simp only [if_neg hb]
      exact Nat.even_iff.mp (Nat.not_odd_iff_even.mp
        (fun ho => hb ((D.cnt_odd_iff h₁ h₂ b (hY₁ b) (hY₂ b)).mp ho)))
  rw [Nat.even_iff, Nat.even_iff, key]

/-- An inner generator commutes with the inner logical `X` (it lies in `Cin`'s stabilizer,
which the logical centralizes). -/
lemma inner_gen_comm_logicalX (g : NQubitPauliGroupElement n₁)
    (hg : g ∈ NQubitPauliGroupElement.listToSet D.Cin.generatorsList) :
    g * (D.Cin.logicalOps 0).xOp = (D.Cin.logicalOps 0).xOp * g :=
  (mem_centralizer_iff _ _).mp (D.Cin.logicalOps 0).x_mem_centralizer g
    (Subgroup.subset_closure hg)

/-- An inner generator commutes with the inner logical `Z`. -/
lemma inner_gen_comm_logicalZ (g : NQubitPauliGroupElement n₁)
    (hg : g ∈ NQubitPauliGroupElement.listToSet D.Cin.generatorsList) :
    g * (D.Cin.logicalOps 0).zOp = (D.Cin.logicalOps 0).zOp * g :=
  (mem_centralizer_iff _ _).mp (D.Cin.logicalOps 0).z_mem_centralizer g
    (Subgroup.subset_closure hg)

/-- An inner generator commutes with the zero-phase embedding of any single-qubit promotion
`I ↦ 1`, `X ↦ X̄`, `Z ↦ Z̄` (the `Y` branch is excluded). -/
lemma inner_gen_comm_promoteSingle (g : NQubitPauliGroupElement n₁)
    (hg : g ∈ NQubitPauliGroupElement.listToSet D.Cin.generatorsList)
    (P : PauliOperator) (hPY : P ≠ PauliOperator.Y) :
    g * ofOperator (promoteSingle D.Xbar D.Zbar P)
      = ofOperator (promoteSingle D.Xbar D.Zbar P) * g := by
  rcases P with _ | _ | _ | _
  · change g * (1 : NQubitPauliGroupElement n₁) = 1 * g
    rw [mul_one, one_mul]
  · rw [show promoteSingle D.Xbar D.Zbar PauliOperator.X = D.Xbar from rfl, D.ofOperator_Xbar]
    exact D.inner_gen_comm_logicalX g hg
  · exact absurd rfl hPY
  · rw [show promoteSingle D.Xbar D.Zbar PauliOperator.Z = D.Zbar from rfl, D.ofOperator_Zbar]
    exact D.inner_gen_comm_logicalZ g hg

/-- An embedded inner generator commutes with any promoted (`Y`-free) outer operator:
they agree where the inner operator is non-`I` (block `b`), reducing to the inner generator
commuting with the inner logical there. -/
lemma embedBlock_promoteE_commute (b : Fin n₂) (g : NQubitPauliGroupElement n₁)
    (hg : g ∈ NQubitPauliGroupElement.listToSet D.Cin.generatorsList)
    (h : NQubitPauliGroupElement n₂) (hhY : ∀ b', h.operators b' ≠ PauliOperator.Y) :
    embedBlock b g * promoteE D.Xbar D.Zbar h
      = promoteE D.Xbar D.Zbar h * embedBlock b g := by
  classical
  rw [commutes_iff_even_anticommutes]
  have hpred : anticommutesAt (embedBlock b g).operators (promoteE D.Xbar D.Zbar h).operators
      = anticommutesAt (embedBlock b g).operators
          (embedBlock b (ofOperator (promoteSingle D.Xbar D.Zbar (h.operators b)))).operators := by
    funext q
    by_cases hbq : blockOf q = b
    · have hval : (promoteE D.Xbar D.Zbar h).operators q
          = (embedBlock b
              (ofOperator (promoteSingle D.Xbar D.Zbar (h.operators b)))).operators q := by
        simp [embedBlock_operators, embedBlockOp, promoteE_operators, promoteOp, hbq]
      unfold NQubitPauliGroupElement.anticommutesAt
      rw [hval]
    · have hI : (embedBlock b g).operators q = PauliOperator.I := by
        simp [embedBlock_operators, embedBlockOp, hbq]
      rw [eq_iff_iff]
      constructor <;> intro hac <;>
        exact absurd hac (not_anticommutesAt_of_left_I _ _ q hI)
  rw [hpred, ← commutes_iff_even_anticommutes, embedBlock_commute_iff]
  exact D.inner_gen_comm_promoteSingle g hg (h.operators b) (hhY b)

/-- The typed outer generators are `Y`-free (Z-type or X-type). -/
lemma outer_gen_noY (y : NQubitPauliGroupElement n₂) (hy : y ∈ D.outerZ ++ D.outerX) :
    ∀ b', y.operators b' ≠ PauliOperator.Y := by
  intro b'
  rcases List.mem_append.mp hy with hz | hx
  · rcases (D.outerZ_isZ y hz).2 b' with h | h <;> rw [h] <;> decide
  · rcases (D.outerX_isX y hx).2 b' with h | h <;> rw [h] <;> decide

/-- Membership in the concatenated generator list: every element is an embedded inner
generator or a promoted (typed) outer generator. -/
lemma mem_concatGeneratorsList (x : NQubitPauliGroupElement (n₁ * n₂))
    (hx : x ∈ NQubitPauliGroupElement.listToSet D.concatGeneratorsList) :
    (∃ b z, z ∈ NQubitPauliGroupElement.listToSet D.Cin.generatorsList ∧ embedBlock b z = x) ∨
      (∃ y, y ∈ D.outerZ ++ D.outerX ∧ promoteE D.Xbar D.Zbar y = x) := by
  simp only [NQubitPauliGroupElement.listToSet, Set.mem_setOf_eq,
    ConcatCSSData.concatGeneratorsList, ConcatCSSData.s1PerBlockList,
    ConcatCSSData.promotedOuterList, List.mem_append, List.mem_flatMap, List.mem_map] at hx
  rcases hx with ⟨b, _, z, hz, rfl⟩ | ⟨y, hy, rfl⟩
  · exact Or.inl ⟨b, z, hz, rfl⟩
  · exact Or.inr ⟨y, List.mem_append.mpr hy, rfl⟩

/-- All concatenated generators pairwise commute. -/
lemma concat_generators_commute :
    ∀ g ∈ NQubitPauliGroupElement.listToSet D.concatGeneratorsList,
      ∀ h ∈ NQubitPauliGroupElement.listToSet D.concatGeneratorsList, g * h = h * g := by
  intro g hg h hh
  rcases D.mem_concatGeneratorsList g hg with ⟨b₁, z₁, hz₁, rfl⟩ | ⟨y₁, hy₁, rfl⟩ <;>
    rcases D.mem_concatGeneratorsList h hh with ⟨b₂, z₂, hz₂, rfl⟩ | ⟨y₂, hy₂, rfl⟩
  · by_cases hbb : b₁ = b₂
    · subst hbb
      rw [embedBlock_commute_iff]
      exact D.Cin.generators_commute z₁ hz₁ z₂ hz₂
    · exact embedBlock_cross_commute hbb z₁ z₂
  · exact D.embedBlock_promoteE_commute b₁ z₁ hz₁ y₂ (D.outer_gen_noY y₂ hy₂)
  · exact (D.embedBlock_promoteE_commute b₂ z₂ hz₂ y₁ (D.outer_gen_noY y₁ hy₁)).symm
  · rw [commutes_iff_even_anticommutes,
      D.promote_anticommute_parity y₁ y₂ (D.outer_gen_noY y₁ hy₁) (D.outer_gen_noY y₂ hy₂),
      ← commutes_iff_even_anticommutes]
    exact D.Cout.generators_commute y₁ (D.outer_split.mem_iff.mpr hy₁)
      y₂ (D.outer_split.mem_iff.mpr hy₂)

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
