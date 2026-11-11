import QEC.Stabilizer.Framework.Concatenation.Independence

/-!
# Concatenation: the concatenated code

From a `ConcatCSSData`, this file builds the concatenated code on `n₁ * n₂`
qubits with `k₂` logical qubits.

- `promoteE_commute_iff` and `promoteE_anticommute_iff`: promotion preserves
  commutation and anticommutation of outer elements without `Y` factors,
  because it preserves the symplectic inner product.
- `embedBlock_promoteE_commute`: an element of the inner stabilizer group
  embedded in a block commutes with every promoted outer element.
- `concat_generators_commute` and `concat_closure_no_neg_identity`: the
  concatenated generators pairwise commute and do not generate `−I`, so they
  generate a stabilizer group `concatStabGroup`.
- `concatLogicalOps`: the promoted outer logical operators are logical
  operators of the concatenated code.
- `promoteE_rep_mem_centralizer`: promoting an `X`-type element of the outer
  centralizer along any element of the inner centralizer of logical class `X`
  gives an element of the centralizer of `concatStabGroup`.
- `concatPresentation`, `concatenate` and `concatenateWithLogicals`: the
  concatenated code as a presentation, as a `StabilizerCode (n₁ * n₂) k₂`, and
  with its logical basis.
-/

namespace Quantum.Concatenation

open NQubitPauliGroupElement NQubitPauliOperator StabilizerGroup

variable {n₁ n₂ k₂ : ℕ}

namespace ConcatCSSData

variable (D : ConcatCSSData n₁ n₂ k₂)

/-! ## Commutation of promoted and embedded elements -/

/-- Promotion preserves the symplectic inner product of outer elements without
`Y` factors. -/
theorem symplecticInner_promoteE {h₁ h₂ : NQubitPauliGroupElement n₂}
    (hY₁ : ∀ b, h₁.operators b ≠ PauliOperator.Y) (hY₂ : ∀ b, h₂.operators b ≠ PauliOperator.Y) :
    ⟪promoteE D.Xbar D.Zbar h₁, promoteE D.Xbar D.Zbar h₂⟫ₛ = ⟪h₁, h₂⟫ₛ :=
  symplecticInner_promoteOp_promoteOp D.symplecticInner_Xbar_Zbar hY₁ hY₂

/-- The promotions of two outer elements without `Y` factors commute iff the
outer elements do. -/
theorem promoteE_commute_iff {h₁ h₂ : NQubitPauliGroupElement n₂}
    (hY₁ : ∀ b, h₁.operators b ≠ PauliOperator.Y) (hY₂ : ∀ b, h₂.operators b ≠ PauliOperator.Y) :
    promoteE D.Xbar D.Zbar h₁ * promoteE D.Xbar D.Zbar h₂ =
        promoteE D.Xbar D.Zbar h₂ * promoteE D.Xbar D.Zbar h₁ ↔
      h₁ * h₂ = h₂ * h₁ := by
  rw [commutes_iff_symplectic_inner_zero, commutes_iff_symplectic_inner_zero,
    D.symplecticInner_promoteE hY₁ hY₂]

/-- The promotions of two outer elements without `Y` factors anticommute iff
the outer elements do. -/
theorem promoteE_anticommute_iff {h₁ h₂ : NQubitPauliGroupElement n₂}
    (hY₁ : ∀ b, h₁.operators b ≠ PauliOperator.Y) (hY₂ : ∀ b, h₂.operators b ≠ PauliOperator.Y) :
    Anticommute (promoteE D.Xbar D.Zbar h₁) (promoteE D.Xbar D.Zbar h₂) ↔ Anticommute h₁ h₂ := by
  rw [anticommutes_iff_symplectic_inner_one, anticommutes_iff_symplectic_inner_one,
    D.symplecticInner_promoteE hY₁ hY₂]

/-- The logical class of an inner element is `I` iff it commutes with both
inner logical operators. -/
lemma logicalClass_eq_I_iff_commute (r : NQubitPauliGroupElement n₁) :
    logicalClass D.Xbar D.Zbar r.operators = PauliOperator.I ↔
      r * D.Cin.logicalX 0 = D.Cin.logicalX 0 * r ∧
        r * D.Cin.logicalZ 0 = D.Cin.logicalZ 0 * r := by
  rw [logicalClass_eq_I_iff, commutes_iff_symplectic_inner_zero,
    commutes_iff_symplectic_inner_zero]
  rfl

/-- The logical class of an inner element is `X` iff it commutes with the inner
logical `X` and anticommutes with the inner logical `Z`. -/
lemma logicalClass_eq_X_iff_commute (r : NQubitPauliGroupElement n₁) :
    logicalClass D.Xbar D.Zbar r.operators = PauliOperator.X ↔
      r * D.Cin.logicalX 0 = D.Cin.logicalX 0 * r ∧ Anticommute r (D.Cin.logicalZ 0) := by
  rw [logicalClass_eq_X_iff, commutes_iff_symplectic_inner_zero,
    anticommutes_iff_symplectic_inner_one]
  rfl

/-- An element of the inner stabilizer group has logical class `I`: it commutes
with both inner logical operators. -/
lemma logicalClass_of_mem_Cin {s : NQubitPauliGroupElement n₁}
    (hs : s ∈ D.Cin.toStabilizerGroup.toSubgroup) :
    logicalClass D.Xbar D.Zbar s.operators = PauliOperator.I :=
  (D.logicalClass_eq_I_iff_commute s).mpr
    ⟨(mem_centralizer_iff _ _).mp (D.Cin.logicalOps 0).x_mem_centralizer s hs,
      (mem_centralizer_iff _ _).mp (D.Cin.logicalOps 0).z_mem_centralizer s hs⟩

/-- An element of the inner stabilizer group embedded in a block commutes with
the promotion of every outer element without `Y` factors: on that block the
promotion is the identity or an inner logical operator. -/
lemma embedBlock_promoteE_commute (b : Fin n₂) {s : NQubitPauliGroupElement n₁}
    (hs : s ∈ D.Cin.toStabilizerGroup.toSubgroup) {h : NQubitPauliGroupElement n₂}
    (hY : ∀ b, h.operators b ≠ PauliOperator.Y) :
    embedBlock b s * promoteE D.Xbar D.Zbar h = promoteE D.Xbar D.Zbar h * embedBlock b s := by
  rw [commutes_iff_symplectic_inner_zero, embedBlock_operators, promoteE_operators,
    symplecticInner_embedBlockOp_left, restrictBlockOp_promoteOp,
    symplecticInner_promoteSingle _ _ _ (hY b), D.logicalClass_of_mem_Cin hs,
    PauliOperator.symplecticProductSingle_I_left]

/-! ## The stabilizer group of the concatenated code -/

/-- The concatenated generators pairwise commute. -/
theorem concat_generators_commute :
    ∀ g ∈ D.concatGeneratorsList, ∀ h ∈ D.concatGeneratorsList, g * h = h * g := by
  intro g hg h hh
  obtain ⟨b₁, z₁, hz₁, rfl⟩ | ⟨y₁, hy₁, rfl⟩ := D.mem_concatGeneratorsList.mp hg <;>
    obtain ⟨b₂, z₂, hz₂, rfl⟩ | ⟨y₂, hy₂, rfl⟩ := D.mem_concatGeneratorsList.mp hh
  · by_cases hbb : b₁ = b₂
    · subst hbb
      exact (embedBlock_commute_iff b₁ z₁ z₂).mpr (D.Pin.generators_commute z₁ hz₁ z₂ hz₂)
    · exact embedBlock_cross_commute hbb z₁ z₂
  · exact D.embedBlock_promoteE_commute b₁ (D.mem_Cin_of_mem_gens hz₁) (D.outer_gen_noY hy₂)
  · exact (D.embedBlock_promoteE_commute b₂ (D.mem_Cin_of_mem_gens hz₂)
      (D.outer_gen_noY hy₁)).symm
  · exact (D.promoteE_commute_iff (D.outer_gen_noY hy₁) (D.outer_gen_noY hy₂)).mpr
      (D.Pout.generators_commute y₁ (D.outer_split.mem_iff.mpr hy₁)
        y₂ (D.outer_split.mem_iff.mpr hy₂))

/-- The concatenated generators do not generate `−I`: they split into `Z`-type
generators (the embedded `Z`-type inner generators and the promoted `Z`-type
outer generators) and `X`-type generators, which commute with each other. -/
theorem concat_closure_no_neg_identity :
    negIdentity (n₁ * n₂) ∉ Subgroup.closure (listToSet D.concatGeneratorsList) := by
  have hset : listToSet D.concatGeneratorsList =
      {g | (∃ b, ∃ z ∈ D.innerZ, embedBlock b z = g) ∨
           (∃ y ∈ D.outerZ, promoteE D.Xbar D.Zbar y = g)} ∪
      {g | (∃ b, ∃ x ∈ D.innerX, embedBlock b x = g) ∨
           (∃ y ∈ D.outerX, promoteE D.Xbar D.Zbar y = g)} := by
    ext g
    simp only [Set.mem_union, Set.mem_setOf_eq, listToSet, D.mem_concatGeneratorsList,
      List.mem_append, D.inner_split.mem_iff, or_and_right, exists_or]
    rw [or_or_or_comm]
  rw [hset]
  refine CSS.negIdentity_not_mem_closure_union _ _ ?_ ?_ fun z hz x hx =>
    D.concat_generators_commute z (hset.symm.subset (Or.inl hz)) x (hset.symm.subset (Or.inr hx))
  · rintro z (⟨b, w, hw, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact embedBlock_isZ b (D.innerZ_isZ w hw)
    · exact promoteE_isZ D.innerLogZ_isZ (D.outerZ_isZ y hy).2
  · rintro x (⟨b, w, hw, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact embedBlock_isX b (D.innerX_isX w hw)
    · exact promoteE_isX D.innerLogX_isX (D.outerX_isX y hy).2

/-- The stabilizer group of the concatenated code, generated by
`concatGeneratorsList`. -/
noncomputable def concatStabGroup : StabilizerGroup (n₁ * n₂) :=
  mkStabilizerFromGenerators (n₁ * n₂) D.concatGeneratorsList
    D.concat_generators_commute D.concat_closure_no_neg_identity

/-- An inner generator embedded in a block is in the concatenated stabilizer
group. -/
lemma embedBlock_mem_concatStabGroup (b : Fin n₂) {s : NQubitPauliGroupElement n₁}
    (hs : s ∈ D.Pin.generatorsList) : embedBlock b s ∈ D.concatStabGroup.toSubgroup :=
  Subgroup.subset_closure (D.embedBlock_mem_concatGeneratorsList b hs)

/-- A promoted outer generator is in the concatenated stabilizer group. -/
lemma promoteE_mem_concatStabGroup {y : NQubitPauliGroupElement n₂}
    (hy : y ∈ D.outerZ ++ D.outerX) :
    promoteE D.Xbar D.Zbar y ∈ D.concatStabGroup.toSubgroup :=
  Subgroup.subset_closure (D.promoteE_mem_concatGeneratorsList hy)

/-! ## The logical operators of the concatenated code -/

/-- The promotion of an element of the outer centralizer without `Y` factors
lies in the centralizer of the concatenated stabilizer group. -/
lemma promoteE_mem_centralizer {h : NQubitPauliGroupElement n₂}
    (hY : ∀ b, h.operators b ≠ PauliOperator.Y)
    (hh : h ∈ centralizer D.Cout.toStabilizerGroup) :
    promoteE D.Xbar D.Zbar h ∈ centralizer D.concatStabGroup := by
  refine (mem_centralizer_iff_closure _ _ _ rfl).mpr fun s hs => ?_
  obtain ⟨b, z, hz, rfl⟩ | ⟨y, hy, rfl⟩ := D.mem_concatGeneratorsList.mp hs
  · exact D.embedBlock_promoteE_commute b (D.mem_Cin_of_mem_gens hz) hY
  · exact (D.promoteE_commute_iff (D.outer_gen_noY hy) hY).mpr
      ((mem_centralizer_iff _ _).mp hh y (D.mem_Cout_of_mem_gens (D.outer_split.mem_iff.mpr hy)))

/-- Promoting an `X`-type element `h` of the outer centralizer along an element
`x` of the inner centralizer of logical class `X` gives an element of the
centralizer of the concatenated stabilizer group. On each block it is `x` or
the identity, which commute with the inner generators; and it induces `h`,
which commutes with the outer generators.

For `x` the inner logical `X` this is `promoteE_mem_centralizer`; a
representative `x` of smaller weight gives a logical operator of smaller
weight. -/
lemma promoteE_rep_mem_centralizer {x : NQubitPauliGroupElement n₁}
    (hx : x ∈ centralizer D.Cin.toStabilizerGroup)
    (hxX : logicalClass D.Xbar D.Zbar x.operators = PauliOperator.X)
    {h : NQubitPauliGroupElement n₂} (hhX : IsXType h.operators)
    (hh : h ∈ centralizer D.Cout.toStabilizerGroup) :
    promoteE x.operators D.Zbar h ∈ centralizer D.concatStabGroup := by
  refine (mem_centralizer_iff_closure _ _ _ rfl).mpr fun s hs => ?_
  obtain ⟨b, z, hz, rfl⟩ | ⟨y, hy, rfl⟩ := D.mem_concatGeneratorsList.mp hs
  · rw [commutes_iff_symplectic_inner_zero, embedBlock_operators, promoteE_operators,
      symplecticInner_embedBlockOp_left, restrictBlockOp_promoteOp]
    rcases hhX b with hI | hX
    · rw [hI]
      exact symplecticInner_identity_right _
    · rw [hX]
      exact (commutes_iff_symplectic_inner_zero z x).mp
        ((mem_centralizer_iff _ _).mp hx z (D.mem_Cin_of_mem_gens hz))
  · rw [commutes_iff_symplectic_inner_zero, promoteE_operators, promoteE_operators,
      symplecticInner_comm, symplecticInner_promoteOp _ _ _ (D.outer_gen_noY hy),
      inducedOuterOp_promoteOp_of_isXType hxX hhX, symplecticInner_comm]
    exact (commutes_iff_symplectic_inner_zero y h).mp
      ((mem_centralizer_iff _ _).mp hh y (D.mem_Cout_of_mem_gens (D.outer_split.mem_iff.mpr hy)))

/-- The logical `X` of logical qubit `ℓ` of the concatenated code: the promoted
outer logical `X`. -/
def concatLogicalX (ℓ : Fin k₂) : NQubitPauliGroupElement (n₁ * n₂) :=
  promoteE D.Xbar D.Zbar (D.Cout.logicalX ℓ)

/-- The logical `Z` of logical qubit `ℓ` of the concatenated code: the promoted
outer logical `Z`. -/
def concatLogicalZ (ℓ : Fin k₂) : NQubitPauliGroupElement (n₁ * n₂) :=
  promoteE D.Xbar D.Zbar (D.Cout.logicalZ ℓ)

/-- The promoted outer logical `X` commutes with the concatenated stabilizer
group. -/
lemma concatLogicalX_mem_centralizer (ℓ : Fin k₂) :
    D.concatLogicalX ℓ ∈ centralizer D.concatStabGroup :=
  D.promoteE_mem_centralizer (D.outerLogX_isX ℓ).ne_Y (D.Cout.logicalOps ℓ).x_mem_centralizer

/-- The promoted outer logical `Z` commutes with the concatenated stabilizer
group. -/
lemma concatLogicalZ_mem_centralizer (ℓ : Fin k₂) :
    D.concatLogicalZ ℓ ∈ centralizer D.concatStabGroup :=
  D.promoteE_mem_centralizer (D.outerLogZ_isZ ℓ).ne_Y (D.Cout.logicalOps ℓ).z_mem_centralizer

/-- The logical `X` and `Z` of a logical qubit of the concatenated code
anticommute. -/
lemma concatLogical_anticommute (ℓ : Fin k₂) :
    Anticommute (D.concatLogicalX ℓ) (D.concatLogicalZ ℓ) :=
  (D.promoteE_anticommute_iff (D.outerLogX_isX ℓ).ne_Y (D.outerLogZ_isZ ℓ).ne_Y).mpr
    (D.Cout.logicalOps ℓ).anticommute

/-- The logical operators of logical qubit `ℓ` of the concatenated code. -/
def concatLogicalOps (ℓ : Fin k₂) : LogicalQubitOps (n₁ * n₂) D.concatStabGroup where
  xOp := D.concatLogicalX ℓ
  zOp := D.concatLogicalZ ℓ
  x_mem_centralizer := D.concatLogicalX_mem_centralizer ℓ
  z_mem_centralizer := D.concatLogicalZ_mem_centralizer ℓ
  anticommute := D.concatLogical_anticommute ℓ

/-- The logical operators of distinct logical qubits of the concatenated code
commute. -/
lemma concat_logical_commute_cross (ℓ ℓ' : Fin k₂) (hne : ℓ ≠ ℓ') :
    (D.concatLogicalOps ℓ).xOp * (D.concatLogicalOps ℓ').xOp =
        (D.concatLogicalOps ℓ').xOp * (D.concatLogicalOps ℓ).xOp ∧
      (D.concatLogicalOps ℓ).xOp * (D.concatLogicalOps ℓ').zOp =
        (D.concatLogicalOps ℓ').zOp * (D.concatLogicalOps ℓ).xOp ∧
      (D.concatLogicalOps ℓ).zOp * (D.concatLogicalOps ℓ').xOp =
        (D.concatLogicalOps ℓ').xOp * (D.concatLogicalOps ℓ).zOp ∧
      (D.concatLogicalOps ℓ).zOp * (D.concatLogicalOps ℓ').zOp =
        (D.concatLogicalOps ℓ').zOp * (D.concatLogicalOps ℓ).zOp := by
  obtain ⟨hXX, hXZ, hZX, hZZ⟩ := D.Cout.logical_commute_cross ℓ ℓ' hne
  have hX := fun ℓ => (D.outerLogX_isX ℓ).ne_Y
  have hZ := fun ℓ => (D.outerLogZ_isZ ℓ).ne_Y
  exact ⟨(D.promoteE_commute_iff (hX ℓ) (hX ℓ')).mpr hXX,
    (D.promoteE_commute_iff (hX ℓ) (hZ ℓ')).mpr hXZ,
    (D.promoteE_commute_iff (hZ ℓ) (hX ℓ')).mpr hZX,
    (D.promoteE_commute_iff (hZ ℓ) (hZ ℓ')).mpr hZZ⟩

/-! ## The concatenated code -/

/-- The generator-list presentation of the concatenated code. -/
def concatPresentation (D : ConcatCSSData n₁ n₂ k₂) :
    StabilizerCode.Presentation (n₁ * n₂) k₂ where
  hk := D.Cout.hk.trans (Nat.le_mul_of_pos_left n₂ D.Cin.hk)
  generatorsList := D.concatGeneratorsList
  generators_length := D.concatGeneratorsList_length
  generators_phaseZero := D.concatGeneratorsList_phaseZero
  generators_independent := D.rowsLinearIndependent_concat
  generators_commute := D.concat_generators_commute
  closure_no_neg_identity := D.concat_closure_no_neg_identity

/-- The concatenation of an inner CSS code with one logical qubit and an outer
CSS code, as a `StabilizerCode (n₁ * n₂) k₂`: the code presented by
`concatPresentation`. Its stabilizer group is `concatStabGroup`. -/
noncomputable def concatenate (D : ConcatCSSData n₁ n₂ k₂) : StabilizerCode (n₁ * n₂) k₂ :=
  D.concatPresentation.toCode

/-- The concatenated code together with its logical basis, the promoted outer
logical operators `concatLogicalOps`. -/
noncomputable def concatenateWithLogicals (D : ConcatCSSData n₁ n₂ k₂) :
    StabilizerCodeWithLogicals (n₁ * n₂) k₂ where
  toStabilizerCode := D.concatenate
  logicalOps := D.concatLogicalOps
  logical_commute_cross := D.concat_logical_commute_cross

end ConcatCSSData

end Quantum.Concatenation
