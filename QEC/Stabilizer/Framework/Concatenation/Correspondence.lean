import QEC.Stabilizer.Framework.Concatenation.Restriction

/-!
# Concatenation, Tier 2a (part 2): the induced outer logical

Milestone **M5** of the CSS concatenation plan
(`pipeline/attempts/concat_css_general/plan.md`), second half.

For a centralizing element `g` of the concatenated stabilizer, each block
restriction `restrictBlock b g` lies in the inner centralizer (M5 part 1), so by
M4's classification it is either inner-stabilizer-like or a nontrivial inner
logical. The **induced outer operator** `inducedOuter D g` records, per block, the
inner logical *class* of that restriction — read off from how it commutes with the
inner logicals `X̄₁`, `Z̄₁`:

* commutes with both → `I` (stabilizer-like);
* anticommutes with `Z̄₁` only → `X`;
* anticommutes with `X̄₁` only → `Z`;
* anticommutes with both → `Y`.

The key bridge `induced_anticommute_parity` says, for a `Y`-free outer operator
`h`, that `inducedOuter D g` anticommutes with `h` exactly when `g` anticommutes
with the promoted `h` — the dual of the M3 parity core. From it:

* `inducedOuter_support_eq` — block `b` is in the support iff `restrictBlock b g`
  is a nontrivial inner logical (uses M4);
* `inducedOuter_mem_centralizer` — `inducedOuter D g` centralizes the outer
  stabilizer.

(`inducedOuter_not_mem_stabilizer` / `inducedOuter_isNontrivialLogical`, the coset
injectivity of plan risk R7, are developed separately.)
-/

namespace Quantum.Concatenation

open NQubitPauliGroupElement StabilizerGroup

variable {n₁ n₂ k₂ : ℕ} [NeZero n₁]

/-! ## The induced outer operator -/

open Classical in
/-- The inner logical class of block `b`'s restriction, read off from its commutation with
the inner logicals: `I` if it commutes with both, `X`/`Z` for a single anticommutation,
`Y` for both. -/
noncomputable def inducedOuterOp (D : ConcatCSSData n₁ n₂ k₂)
    (g : NQubitPauliGroupElement (n₁ * n₂)) : NQubitPauliOperator n₂ :=
  fun b =>
    if Anticommute (restrictBlock b g) (D.Cin.logicalOps 0).zOp then
      (if Anticommute (restrictBlock b g) (D.Cin.logicalOps 0).xOp
        then PauliOperator.Y else PauliOperator.X)
    else
      (if Anticommute (restrictBlock b g) (D.Cin.logicalOps 0).xOp
        then PauliOperator.Z else PauliOperator.I)

/-- The induced outer operator as a phase-0 group element. -/
noncomputable def inducedOuter (D : ConcatCSSData n₁ n₂ k₂)
    (g : NQubitPauliGroupElement (n₁ * n₂)) : NQubitPauliGroupElement n₂ :=
  ofOperator (inducedOuterOp D g)

@[simp] lemma inducedOuter_operators (D : ConcatCSSData n₁ n₂ k₂)
    (g : NQubitPauliGroupElement (n₁ * n₂)) :
    (inducedOuter D g).operators = inducedOuterOp D g := rfl

namespace ConcatCSSData

variable (D : ConcatCSSData n₁ n₂ k₂)

/-- The induced class at `b` is `I` exactly when the restriction commutes with both inner
logicals. -/
lemma inducedOuterOp_eq_I_iff (g : NQubitPauliGroupElement (n₁ * n₂)) (b : Fin n₂) :
    inducedOuterOp D g b = PauliOperator.I
      ↔ ¬ Anticommute (restrictBlock b g) (D.Cin.logicalOps 0).zOp
        ∧ ¬ Anticommute (restrictBlock b g) (D.Cin.logicalOps 0).xOp := by
  unfold inducedOuterOp
  split_ifs with h1 h2 h3
  · exact iff_of_false (by decide) (fun hc => hc.1 h1)
  · exact iff_of_false (by decide) (fun hc => hc.1 h1)
  · exact iff_of_false (by decide) (fun hc => hc.2 h3)
  · exact iff_of_true rfl ⟨h1, h3⟩

/-- **(Per-block bridge.)** For a `Y`-free entry `h.operators b`, the induced operator
anticommutes with `h` at block `b` exactly when the restriction anticommutes with the
promoted single-qubit Pauli `ofOperator (promoteSingle … (h.operators b))` (= `1`, `X̄₁`, or
`Z̄₁`). The single-block analogue of `cnt_odd_iff`. -/
lemma induced_block_anticommute_iff (g : NQubitPauliGroupElement (n₁ * n₂))
    (h : NQubitPauliGroupElement n₂) (b : Fin n₂)
    (hP : h.operators b ≠ PauliOperator.Y) :
    NQubitPauliGroupElement.anticommutesAt (inducedOuterOp D g) h.operators b
      ↔ Anticommute (restrictBlock b g)
          (ofOperator (promoteSingle D.Xbar D.Zbar (h.operators b))) := by
  rcases hPb : h.operators b with _ | _ | _ | _
  · -- I: both sides false
    refine iff_of_false (not_anticommutesAt_of_right_I _ _ b hPb) ?_
    simp only [promoteSingle, ofOperator_identity]
    exact not_anticommute_one_right _
  · -- X: both sides ↔ anticommuting with X̄₁ (the Z-component bit)
    rw [show ofOperator (promoteSingle D.Xbar D.Zbar PauliOperator.X)
        = (D.Cin.logicalOps 0).xOp from by simp only [promoteSingle]; exact D.ofOperator_Xbar]
    simp only [NQubitPauliGroupElement.anticommutesAt, inducedOuterOp, hPb]
    split_ifs with h1 h2 h3 <;>
      first
        | exact iff_of_true (by decide) (by assumption)
        | exact iff_of_false (by decide) (by assumption)
  · exact absurd hPb hP
  · -- Z: both sides ↔ anticommuting with Z̄₁ (the X-component bit)
    rw [show ofOperator (promoteSingle D.Xbar D.Zbar PauliOperator.Z)
        = (D.Cin.logicalOps 0).zOp from by simp only [promoteSingle]; exact D.ofOperator_Zbar]
    simp only [NQubitPauliGroupElement.anticommutesAt, inducedOuterOp, hPb]
    split_ifs with h1 h2 h3 <;>
      first
        | exact iff_of_true (by decide) (by assumption)
        | exact iff_of_false (by decide) (by assumption)

/-- Per-position reduction for the induced bridge: `g` anticommutes with the promoted `h` at
`q` exactly when the restriction anticommutes with the single-qubit promotion of `h.operators b`
at `posOf q` (within block `b = blockOf q`). -/
lemma anticommutesAt_g_promoteE (g : NQubitPauliGroupElement (n₁ * n₂))
    (h : NQubitPauliGroupElement n₂) (b : Fin n₂) (q : Fin (n₁ * n₂)) (hb : blockOf q = b) :
    NQubitPauliGroupElement.anticommutesAt g.operators (promoteE D.Xbar D.Zbar h).operators q
      ↔ NQubitPauliGroupElement.anticommutesAt (restrictBlock b g).operators
          (promoteSingle D.Xbar D.Zbar (h.operators b)) (posOf q) := by
  have hval1 : (promoteE D.Xbar D.Zbar h).operators q
      = promoteSingle D.Xbar D.Zbar (h.operators b) (posOf q) := by
    simp only [promoteE_operators, promoteOp, hb]
  have hval2 : g.operators q = (restrictBlock b g).operators (posOf q) := by
    change g.operators q = g.operators (qIdx b (posOf q))
    congr 1; rw [← hb]; exact (qIdx_blockOf_posOf q).symm
  unfold NQubitPauliGroupElement.anticommutesAt
  rw [hval1, hval2]

open Classical in
/-- Block-decomposition: the anticommuting-position count of `g` against a promoted outer
operator is the sum over blocks of the per-block restriction-vs-promotion counts. The mixed
analogue of `promote_count_eq_sum`. -/
lemma count_promoteE_eq_sum_restrict (g : NQubitPauliGroupElement (n₁ * n₂))
    (h : NQubitPauliGroupElement n₂) :
    (Finset.univ.filter
        (anticommutesAt g.operators (promoteE D.Xbar D.Zbar h).operators)).card
      = ∑ b : Fin n₂, (Finset.univ.filter (anticommutesAt (restrictBlock b g).operators
          (promoteSingle D.Xbar D.Zbar (h.operators b)))).card := by
  rw [Finset.card_eq_sum_card_fiberwise (fun q _ => Finset.mem_univ (blockOf q))]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.filter_filter]
  have himg : Finset.univ.filter (fun q => anticommutesAt g.operators
        (promoteE D.Xbar D.Zbar h).operators q ∧ blockOf q = b)
      = (Finset.univ.filter (anticommutesAt (restrictBlock b g).operators
          (promoteSingle D.Xbar D.Zbar (h.operators b)))).image (qIdx b) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hac, hb⟩
      exact ⟨posOf q, (D.anticommutesAt_g_promoteE g h b q hb).mp hac,
        by rw [← hb]; exact qIdx_blockOf_posOf q⟩
    · rintro ⟨i, hi, rfl⟩
      refine ⟨(D.anticommutesAt_g_promoteE g h b (qIdx b i) (blockOf_qIdx b i)).mpr ?_,
        blockOf_qIdx b i⟩
      rw [posOf_qIdx]; exact hi
  rw [himg, Finset.card_image_of_injective _ (fun i i' h => (qIdx_injective h).2)]

open Classical in
/-- **(Induced parity bridge.)** For a `Y`-free outer operator `h`, the anticommuting-position
count of the induced operator against `h` has the same parity as that of `g` against the
promoted `h`. The dual of `promote_anticommute_parity`. -/
lemma induced_count_mod_two (g : NQubitPauliGroupElement (n₁ * n₂))
    (h : NQubitPauliGroupElement n₂) (hY : ∀ b, h.operators b ≠ PauliOperator.Y) :
    (Finset.univ.filter (anticommutesAt (inducedOuterOp D g) h.operators)).card % 2
      = (Finset.univ.filter
          (anticommutesAt g.operators (promoteE D.Xbar D.Zbar h).operators)).card % 2 := by
  rw [D.count_promoteE_eq_sum_restrict g h, Finset.card_filter]
  conv_rhs => rw [Finset.sum_nat_mod]
  congr 1
  refine Finset.sum_congr rfl (fun b _ => ?_)
  by_cases hac : anticommutesAt (inducedOuterOp D g) h.operators b
  · simp only [if_pos hac]
    exact (Nat.odd_iff.mp ((anticommutes_iff_odd_anticommutes _ _).mp
      ((D.induced_block_anticommute_iff g h b (hY b)).mp hac))).symm
  · simp only [if_neg hac]
    exact (Nat.even_iff.mp (Nat.not_odd_iff_even.mp (fun ho => hac
      ((D.induced_block_anticommute_iff g h b (hY b)).mpr
        ((anticommutes_iff_odd_anticommutes _ _).mpr ho))))).symm

/-- **(M5.)** For a `Y`-free outer operator `h`, the induced operator commutes with `h` iff `g`
commutes with the promoted `h`. -/
lemma induced_commute_iff (g : NQubitPauliGroupElement (n₁ * n₂))
    (h : NQubitPauliGroupElement n₂) (hY : ∀ b, h.operators b ≠ PauliOperator.Y) :
    inducedOuter D g * h = h * inducedOuter D g
      ↔ g * promoteE D.Xbar D.Zbar h = promoteE D.Xbar D.Zbar h * g := by
  rw [commutes_iff_even_anticommutes (inducedOuter D g) h,
    commutes_iff_even_anticommutes g (promoteE D.Xbar D.Zbar h), inducedOuter_operators,
    Nat.even_iff, Nat.even_iff, D.induced_count_mod_two g h hY]

/-- A promoted outer generator is one of the concatenated generators. -/
lemma promoteE_mem_concatGeneratorsList (y : NQubitPauliGroupElement n₂)
    (hy : y ∈ D.outerZ ++ D.outerX) :
    promoteE D.Xbar D.Zbar y ∈ NQubitPauliGroupElement.listToSet D.concatGeneratorsList := by
  simp only [NQubitPauliGroupElement.listToSet, Set.mem_setOf_eq,
    ConcatCSSData.concatGeneratorsList, ConcatCSSData.promotedOuterList, List.mem_append,
    List.mem_map]
  exact Or.inr ⟨y, List.mem_append.mp hy, rfl⟩

/-- **(M5.)** The induced outer operator centralizes the outer stabilizer: for each outer
generator `y`, `inducedOuter D g` commutes with `y` because `g` commutes with `promoteE y`
(a concatenated generator) and the induced bridge transports that commutation. -/
theorem inducedOuter_mem_centralizer (g : NQubitPauliGroupElement (n₁ * n₂))
    (hg : g ∈ centralizer D.concatStabGroup) :
    inducedOuter D g ∈ centralizer D.Cout.toStabilizerGroup := by
  apply CentralizerLemmas.mem_centralizer_of_commutes_list _ _ D.Cout.generatorsList rfl
  intro y hy
  have hymem : y ∈ D.outerZ ++ D.outerX := D.outer_split.mem_iff.mp hy
  have hyY : ∀ b, y.operators b ≠ PauliOperator.Y := D.outer_gen_noY y hymem
  have hprommem : promoteE D.Xbar D.Zbar y ∈ D.concatStabGroup.toSubgroup :=
    Subgroup.subset_closure (D.promoteE_mem_concatGeneratorsList y hymem)
  have hcommg : g * promoteE D.Xbar D.Zbar y = promoteE D.Xbar D.Zbar y * g :=
    ((mem_centralizer_iff g D.concatStabGroup).mp hg (promoteE D.Xbar D.Zbar y) hprommem).symm
  exact ((D.induced_commute_iff g y hyY).mpr hcommg).symm

/-! ## Support of the induced operator: nontrivial-block characterisation (uses M4) -/

/-- For Pauli group elements, commuting precludes anticommuting. -/
lemma commute_not_anticommute {m : ℕ} {p q : NQubitPauliGroupElement m}
    (h : p * q = q * p) : ¬ Anticommute p q := by
  intro hanti
  rw [Anticommute, h] at hanti
  exact one_ne_minusOne (mul_right_cancel (b := q * p) (by rw [one_mul]; exact hanti))

/-- **(Uses M4.)** A block restriction commutes with both inner logicals iff its operator part
is realised by an inner stabilizer. Forward is M4's decisive kernel; backward is operator-part
commutation (the restriction and the matching stabilizer share an operator part, and the
logicals centralise the stabilizer). -/
lemma restrict_commutes_both_iff_stab (g : NQubitPauliGroupElement (n₁ * n₂))
    (hg : g ∈ centralizer D.concatStabGroup)
    (hindep : rowsLinearIndependent D.Cin.generatorsList) (b : Fin n₂) :
    (¬ Anticommute (restrictBlock b g) (D.Cin.logicalOps 0).zOp
      ∧ ¬ Anticommute (restrictBlock b g) (D.Cin.logicalOps 0).xOp)
    ↔ ∃ s ∈ D.Cin.toStabilizerGroup.toSubgroup, s.operators = (restrictBlock b g).operators := by
  constructor
  · rintro ⟨hZ, hX⟩
    have hcomm_x : restrictBlock b g * (D.Cin.logicalOps 0).xOp
        = (D.Cin.logicalOps 0).xOp * restrictBlock b g :=
      (commute_or_anticommute _ _).resolve_right hX
    have hcomm_z : restrictBlock b g * (D.Cin.logicalOps 0).zOp
        = (D.Cin.logicalOps 0).zOp * restrictBlock b g :=
      (commute_or_anticommute _ _).resolve_right hZ
    exact operators_eq_stab_of_commutes_both_logicals D.Cin hindep (restrictBlock b g)
      (D.restrictBlock_mem_centralizer g hg b) hcomm_x hcomm_z
  · rintro ⟨s, hs, hsop⟩
    refine ⟨commute_not_anticommute ?_, commute_not_anticommute ?_⟩
    · rw [commutes_iff_even_anticommutes, ← hsop, ← commutes_iff_even_anticommutes]
      exact (mem_centralizer_iff (D.Cin.logicalOps 0).zOp D.Cin.toStabilizerGroup).mp
        (D.Cin.logicalOps 0).z_mem_centralizer s hs
    · rw [commutes_iff_even_anticommutes, ← hsop, ← commutes_iff_even_anticommutes]
      exact (mem_centralizer_iff (D.Cin.logicalOps 0).xOp D.Cin.toStabilizerGroup).mp
        (D.Cin.logicalOps 0).x_mem_centralizer s hs

/-- **(M5.)** Block `b` is in the support of the induced outer operator exactly when the
block restriction `restrictBlock b g` is a *nontrivial* inner logical. This is what turns the
per-block weight bound (`weight_ge_of_blocks_ge`) into a count of nontrivial blocks. Uses M4
(`centralizer_classify_of_k1` and the decisive kernel via `restrict_commutes_both_iff_stab`). -/
theorem inducedOuter_support_eq (g : NQubitPauliGroupElement (n₁ * n₂))
    (hg : g ∈ centralizer D.concatStabGroup)
    (hindep : rowsLinearIndependent D.Cin.generatorsList) (b : Fin n₂) :
    b ∈ (inducedOuter D g).support
      ↔ IsNontrivialLogicalOperator (restrictBlock b g) D.Cin.toStabilizerGroup := by
  rw [NQubitPauliGroupElement.mem_support, inducedOuter_operators, ne_eq,
    D.inducedOuterOp_eq_I_iff g b, D.restrict_commutes_both_iff_stab g hg hindep b]
  constructor
  · intro hns
    rcases centralizer_classify_of_k1 D.Cin (restrictBlock b g)
      (D.restrictBlock_mem_centralizer g hg b) with hstab | hnt
    · exact absurd hstab hns
    · exact hnt
  · intro hnt
    rintro ⟨s, hs, hsop⟩
    exact ((IsNontrivialLogicalOperator_iff _ _).mp hnt).2.2 s hs hsop

/-! ## Coset injectivity (plan risk R7 — the remaining M5 sub-pole)

The nontriviality of `inducedOuter D g` rests on a single symplectic fact,
`inducedOuter_symp_in_span` below: if some outer stabilizer `t` has the same operator
part as `inducedOuter D g`, then `g`'s symplectic vector already lies in the span of the
concatenated check matrix — i.e. `g` is concatenated-stabilizer-like. Contrapositively, a
*nontrivial* concatenated logical `g` cannot have a stabilizer-like induced operator, so
`inducedOuter D g` is itself a nontrivial outer logical.

Everything downstream (`inducedOuter_not_mem_stabilizer`, `inducedOuter_isNontrivialLogical`)
is proven unconditionally from this one lemma; only `inducedOuter_symp_in_span` carries a
`sorry`, isolating the genuine content exactly as M4 isolated its dimension kernel. -/

open NQubitPauliOperator in
/-- **(M5, R7 sub-pole — SCOPED.)** Coset injectivity, symplectic form: if an outer
stabilizer `t` matches the operator part of `inducedOuter D g`, then `toSymplectic g.operators`
lies in the concatenated row span (so `g` is stabilizer-like).

**Proof plan (the remaining work).** Writing `restrict b := restrictBlock b g`:

1. `toSymplectic g.operators = ∑ b, toSymplectic (embedBlock b (restrict b)).operators` — `g`
   is the disjoint-support gluing of its block restrictions, so its symplectic vector is the
   (XOR) sum of the embedded block restrictions. [pure index lemma]
2. A symplectic-level embedding map `Lembed b` with
   `toSymplectic (embedBlock b s).operators = Lembed b (toSymplectic s.operators)`, linear, and
   sending `sympSpan Cin.generatorsList` into `sympSpan concatGeneratorsList` (the embedded
   inner generators are concatenated generators). [new symplectic infrastructure]
3. A symplectic-level promotion map with
   `toSymplectic (promoteE Xbar Zbar h).operators ∈ sympSpan concatGeneratorsList` whenever
   `toSymplectic h.operators ∈ sympSpan Cout.generatorsList` (promoted outer generators are
   concatenated generators); in particular for `t ∈ Cout` this gives
   `toSymplectic (promoteE Xbar Zbar t).operators ∈ sympSpan concatGeneratorsList`. [new]
4. Per block, `restrict b` and `restrictBlock b (promoteE Xbar Zbar t) =
   ofOperator (promoteSingle … (t.operators b))` share an inner logical class (because
   `t.operators b = inducedOuterOp D g b`), so their product commutes with both inner logicals
   and is `Cin`-stabilizer-like (M4 kernel). Hence
   `toSymplectic (restrict b).operators + toSymplectic (promoteSingle … (t.operators b)) ∈
   sympSpan Cin.generatorsList`.

Combining (1)+(2)+(4): `toSymplectic g.operators` differs from
`toSymplectic (promoteE Xbar Zbar t).operators` (which is `∑ b` of the embedded
`promoteSingle … (t.operators b)`, by (1) applied to `promoteE … t`) by an element of
`sympSpan concatGeneratorsList`; with (3) the whole vector lands in the span.

The new infrastructure (2)+(3) — `toSymplectic` of `embedBlock` / `promoteE` as linear maps,
and their images inside `sympSpan concatGeneratorsList` — is M4-scale and is the entirety of
the remaining M5 work. -/
lemma inducedOuter_symp_in_span (g : NQubitPauliGroupElement (n₁ * n₂))
    (hg : g ∈ centralizer D.concatStabGroup)
    (hindep : rowsLinearIndependent D.Cin.generatorsList)
    (t : NQubitPauliGroupElement n₂) (ht : t ∈ D.Cout.toStabilizerGroup.toSubgroup)
    (htop : t.operators = (inducedOuter D g).operators) :
    toSymplectic g.operators ∈ sympSpan D.concatGeneratorsList := by
  sorry  -- TODO(concat-m5-r7): symplectic embed/promote infrastructure (see proof plan above)

/-- Coset injectivity: an outer stabilizer matching `inducedOuter D g`'s operator part forces
`g` to be concatenated-stabilizer-like. -/
lemma inducedOuter_coset_injective (g : NQubitPauliGroupElement (n₁ * n₂))
    (hg : g ∈ centralizer D.concatStabGroup)
    (hindep : rowsLinearIndependent D.Cin.generatorsList)
    (t : NQubitPauliGroupElement n₂) (ht : t ∈ D.Cout.toStabilizerGroup.toSubgroup)
    (htop : t.operators = (inducedOuter D g).operators) :
    ∃ S ∈ D.concatStabGroup.toSubgroup, S.operators = g.operators :=
  exists_mem_closure_of_symp_in_span D.concatGeneratorsList g.operators
    (D.inducedOuter_symp_in_span g hg hindep t ht htop)

/-- **(M5.)** The induced outer operator of a *nontrivial* concatenated logical is not an
outer stabilizer (else `g` would be concatenated-stabilizer-like, contradicting nontriviality).
-/
theorem inducedOuter_not_mem_stabilizer (g : NQubitPauliGroupElement (n₁ * n₂))
    (hg : IsNontrivialLogicalOperator g D.concatStabGroup)
    (hindep : rowsLinearIndependent D.Cin.generatorsList) :
    inducedOuter D g ∉ D.Cout.toStabilizerGroup.toSubgroup := by
  intro hmem
  obtain ⟨S, hS, hSop⟩ :=
    D.inducedOuter_coset_injective g hg.1 hindep (inducedOuter D g) hmem rfl
  exact ((IsNontrivialLogicalOperator_iff _ _).mp hg).2.2 S hS hSop

/-- **(M5, headline correspondence.)** The induced outer operator of a nontrivial concatenated
logical is a nontrivial outer logical: it centralizes the outer stabilizer
(`inducedOuter_mem_centralizer`) and its coset is nontrivial (coset injectivity, both the
not-in-stabilizer and the distinct-operator-part clauses). This is the bridge that, with
`inducedOuter_support_eq` and `weight_eq_sum_restrictBlock`, yields the M6 distance bound. -/
theorem inducedOuter_isNontrivialLogical (g : NQubitPauliGroupElement (n₁ * n₂))
    (hg : IsNontrivialLogicalOperator g D.concatStabGroup)
    (hindep : rowsLinearIndependent D.Cin.generatorsList) :
    IsNontrivialLogicalOperator (inducedOuter D g) D.Cout.toStabilizerGroup := by
  refine (IsNontrivialLogicalOperator_iff _ _).mpr
    ⟨D.inducedOuter_mem_centralizer g hg.1, D.inducedOuter_not_mem_stabilizer g hg hindep, ?_⟩
  intro t ht htop
  obtain ⟨S, hS, hSop⟩ := D.inducedOuter_coset_injective g hg.1 hindep t ht htop
  exact ((IsNontrivialLogicalOperator_iff _ _).mp hg).2.2 S hS hSop

end ConcatCSSData

end Quantum.Concatenation
