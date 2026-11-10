import QEC.Stabilizer.Framework.Concatenation.Restriction
import QEC.Stabilizer.Framework.Core
import QEC.Stabilizer.Framework.Symplectic

/-!
# Concatenation: promotion, induced outer operators and the generator list

Concatenation encodes each qubit of an *outer* code into a block carrying an
*inner* code with one logical qubit and logical operators `X̄`, `Z̄`.

- `promoteOp Xbar Zbar h` replaces each single-qubit factor of an outer
  operator `h` by the corresponding inner logical operator on its block:
  `I ↦ I`, `X ↦ X̄`, `Z ↦ Z̄` (`promoteSingle`). A factor `Y` is sent to `I`,
  so promotion is only meaningful for operators without `Y` factors, such as
  `X`-type and `Z`-type operators. `promoteE` is the corresponding Pauli group
  element of phase `+1`.
- `inducedOuterOp Xbar Zbar G` goes the other way: its factor at block `b` is
  the `logicalClass` of the restriction of `G` to block `b`, the single-qubit
  Pauli recording how that restriction commutes with `X̄` and `Z̄`.
- `symplecticInner_promoteOp`: the two maps are adjoint for the symplectic
  inner product, and `inducedOuterOp_promoteOp`: inducing after promoting is
  the identity when `X̄` and `Z̄` anticommute. Hence promotion preserves the
  symplectic inner product (`symplecticInner_promoteOp_promoteOp`).
- `ConcatCSSData n₁ n₂ k₂` bundles an inner CSS code with one logical qubit
  and an outer CSS code, each with a generator list split into `Z`-type and
  `X`-type generators and with CSS-typed logical operators.
- `ConcatCSSData.concatGeneratorsList` is the generator list of the
  concatenated code: the inner generators embedded in every block
  (`s1PerBlockList`), followed by the promoted outer generators
  (`promotedOuterList`).
-/

namespace Quantum

namespace NQubitPauliOperator

variable {n : ℕ}

/-- An `X`-type operator has no `Y` factor. -/
lemma IsXType.ne_Y {op : NQubitPauliOperator n} (h : IsXType op) (i : Fin n) :
    op i ≠ PauliOperator.Y := by
  rcases h i with hi | hi <;> rw [hi] <;> decide

/-- A `Z`-type operator has no `Y` factor. -/
lemma IsZType.ne_Y {op : NQubitPauliOperator n} (h : IsZType op) (i : Fin n) :
    op i ≠ PauliOperator.Y := by
  rcases h i with hi | hi <;> rw [hi] <;> decide

end NQubitPauliOperator

namespace Concatenation

open NQubitPauliGroupElement NQubitPauliOperator StabilizerGroup

variable {n₁ n₂ k₂ : ℕ}

/-! ## The promotion map -/

/-- The inner operator replacing a single-qubit Pauli of an outer operator:
`I ↦ I`, `X ↦ Xbar`, `Z ↦ Zbar`, and `Y ↦ I`. -/
def promoteSingle (Xbar Zbar : NQubitPauliOperator n₁) : PauliOperator → NQubitPauliOperator n₁
  | PauliOperator.I => NQubitPauliOperator.identity n₁
  | PauliOperator.X => Xbar
  | PauliOperator.Z => Zbar
  | PauliOperator.Y => NQubitPauliOperator.identity n₁

/-- The promotion of an outer operator `h` to `n₁ * n₂` qubits: block `b`
carries `promoteSingle Xbar Zbar (h b)`. -/
def promoteOp (Xbar Zbar : NQubitPauliOperator n₁) (h : NQubitPauliOperator n₂) :
    NQubitPauliOperator (n₁ * n₂) :=
  fun q => promoteSingle Xbar Zbar (h (blockOf q)) (posOf q)

/-- The promotion of an outer Pauli group element, as an element of phase `+1`.
The phase of `h` is discarded. -/
def promoteE (Xbar Zbar : NQubitPauliOperator n₁) (h : NQubitPauliGroupElement n₂) :
    NQubitPauliGroupElement (n₁ * n₂) :=
  ofOperator (promoteOp Xbar Zbar h.operators)

@[simp] lemma promoteE_phasePower (Xbar Zbar : NQubitPauliOperator n₁)
    (h : NQubitPauliGroupElement n₂) : (promoteE Xbar Zbar h).phasePower = 0 := rfl

@[simp] lemma promoteE_operators (Xbar Zbar : NQubitPauliOperator n₁)
    (h : NQubitPauliGroupElement n₂) :
    (promoteE Xbar Zbar h).operators = promoteOp Xbar Zbar h.operators := rfl

/-- The restriction of a promoted operator to block `b` is the promotion of
its factor at `b`. -/
@[simp] lemma restrictBlockOp_promoteOp (Xbar Zbar : NQubitPauliOperator n₁) (b : Fin n₂)
    (h : NQubitPauliOperator n₂) :
    restrictBlockOp b (promoteOp Xbar Zbar h) = promoteSingle Xbar Zbar (h b) := by
  funext i
  simp [promoteOp]

/-! ## CSS types of promoted and embedded elements -/

/-- The promotion of a `Z`-type operator along a `Z`-type `Zbar` is a `Z`-type
element. -/
lemma promoteE_isZ {Xbar Zbar : NQubitPauliOperator n₁} (hZbar : IsZType Zbar)
    {h : NQubitPauliGroupElement n₂} (hh : IsZType h.operators) :
    IsZTypeElement (promoteE Xbar Zbar h) := by
  refine ⟨rfl, fun q => ?_⟩
  rcases hh (blockOf q) with hI | hZ
  · exact Or.inl (by simp [promoteOp, promoteSingle, hI, identity])
  · simpa [promoteOp, promoteSingle, hZ] using hZbar (posOf q)

/-- The promotion of an `X`-type operator along an `X`-type `Xbar` is an
`X`-type element. -/
lemma promoteE_isX {Xbar Zbar : NQubitPauliOperator n₁} (hXbar : IsXType Xbar)
    {h : NQubitPauliGroupElement n₂} (hh : IsXType h.operators) :
    IsXTypeElement (promoteE Xbar Zbar h) := by
  refine ⟨rfl, fun q => ?_⟩
  rcases hh (blockOf q) with hI | hX
  · exact Or.inl (by simp [promoteOp, promoteSingle, hI, identity])
  · simpa [promoteOp, promoteSingle, hX] using hXbar (posOf q)

/-- Embedding a `Z`-type element into a block gives a `Z`-type element. -/
lemma embedBlock_isZ (b : Fin n₂) {g : NQubitPauliGroupElement n₁} (hg : IsZTypeElement g) :
    IsZTypeElement (embedBlock b g) := by
  refine ⟨rfl, fun q => ?_⟩
  simp only [embedBlock_operators, embedBlockOp]
  split_ifs
  exacts [hg.2 (posOf q), Or.inl rfl]

/-- Embedding an `X`-type element into a block gives an `X`-type element. -/
lemma embedBlock_isX (b : Fin n₂) {g : NQubitPauliGroupElement n₁} (hg : IsXTypeElement g) :
    IsXTypeElement (embedBlock b g) := by
  refine ⟨rfl, fun q => ?_⟩
  simp only [embedBlock_operators, embedBlockOp]
  split_ifs
  exacts [hg.2 (posOf q), Or.inl rfl]

/-! ## Logical classes and the induced outer operator -/

/-- The logical class of an inner operator `R` relative to the pair `Xbar`,
`Zbar`: the single-qubit Pauli whose `X`-bit is the symplectic inner product
of `R` with `Zbar` and whose `Z`-bit is the symplectic inner product of `R`
with `Xbar`. It is `I` if `R` commutes with both, `X` if `R` anticommutes with
`Zbar` only, `Z` if `R` anticommutes with `Xbar` only, and `Y` if `R`
anticommutes with both. -/
def logicalClass (Xbar Zbar R : NQubitPauliOperator n₁) : PauliOperator :=
  if symplecticInner R Zbar = 0 then
    if symplecticInner R Xbar = 0 then PauliOperator.I else PauliOperator.Z
  else
    if symplecticInner R Xbar = 0 then PauliOperator.X else PauliOperator.Y

/-- The symplectic bits of the logical class of `R` are its symplectic inner
products with `Zbar` and `Xbar`. -/
lemma toSymplecticSingle_logicalClass (Xbar Zbar R : NQubitPauliOperator n₁) :
    (logicalClass Xbar Zbar R).toSymplecticSingle =
      (symplecticInner R Zbar, symplecticInner R Xbar) := by
  have key : ∀ x z : ZMod 2,
      (if x = 0 then (if z = 0 then PauliOperator.I else PauliOperator.Z)
        else (if z = 0 then PauliOperator.X else PauliOperator.Y)).toSymplecticSingle = (x, z) := by
    decide
  exact key _ _

/-- The logical class of `R` is `I` iff `R` is orthogonal to both `Xbar` and
`Zbar`. -/
lemma logicalClass_eq_I_iff {Xbar Zbar R : NQubitPauliOperator n₁} :
    logicalClass Xbar Zbar R = PauliOperator.I ↔
      symplecticInner R Xbar = 0 ∧ symplecticInner R Zbar = 0 := by
  rw [← PauliOperator.toSymplecticSingle_injective.eq_iff, toSymplecticSingle_logicalClass,
    PauliOperator.toSymplecticSingle_I, Prod.mk.injEq, and_comm]

/-- Up to phase, the logical class is multiplicative. -/
lemma logicalClass_mul (Xbar Zbar : NQubitPauliOperator n₁) (r s : NQubitPauliGroupElement n₁) :
    logicalClass Xbar Zbar (r * s).operators =
      ((logicalClass Xbar Zbar r.operators).mulOp
        (logicalClass Xbar Zbar s.operators)).operator := by
  apply PauliOperator.toSymplecticSingle_injective
  rw [PauliOperator.toSymplecticSingle_add]
  simp only [toSymplecticSingle_logicalClass]
  exact congrArg₂ Prod.mk (symplecticInner_mul_left r s (ofOperator Zbar))
    (symplecticInner_mul_left r s (ofOperator Xbar))

/-- Pairing `R` with the promotion of a single-qubit Pauli `P ≠ Y` is the
single-qubit symplectic product of the logical class of `R` with `P`. -/
lemma symplecticInner_promoteSingle (Xbar Zbar R : NQubitPauliOperator n₁) {P : PauliOperator}
    (hP : P ≠ PauliOperator.Y) :
    symplecticInner R (promoteSingle Xbar Zbar P) =
      PauliOperator.symplecticProductSingle (logicalClass Xbar Zbar R) P := by
  cases P
  · rw [PauliOperator.symplecticProductSingle_I_right]
    exact symplecticInner_identity_right R
  · rw [PauliOperator.symplecticProductSingle_X_right, toSymplecticSingle_logicalClass]
    rfl
  · exact absurd rfl hP
  · rw [PauliOperator.symplecticProductSingle_Z_right, toSymplecticSingle_logicalClass]
    rfl

/-- If `Xbar` and `Zbar` anticommute, the logical class of the promotion of a
single-qubit Pauli `P ≠ Y` is `P`. -/
lemma logicalClass_promoteSingle {Xbar Zbar : NQubitPauliOperator n₁}
    (hXZ : symplecticInner Xbar Zbar = 1) {P : PauliOperator} (hP : P ≠ PauliOperator.Y) :
    logicalClass Xbar Zbar (promoteSingle Xbar Zbar P) = P := by
  apply PauliOperator.toSymplecticSingle_injective
  rw [toSymplecticSingle_logicalClass]
  cases P
  · simp [promoteSingle, symplecticInner_identity_left]
  · simp [promoteSingle, hXZ, symplecticInner_self]
  · exact absurd rfl hP
  · simp [promoteSingle, symplecticInner_comm Zbar Xbar, hXZ, symplecticInner_self]

/-- The outer operator induced by an operator `G` on `n₁ * n₂` qubits: its
factor at block `b` is the logical class of the restriction of `G` to block
`b`. -/
def inducedOuterOp (Xbar Zbar : NQubitPauliOperator n₁) (G : NQubitPauliOperator (n₁ * n₂)) :
    NQubitPauliOperator n₂ :=
  fun b => logicalClass Xbar Zbar (restrictBlockOp b G)

/-- Promotion and induction are adjoint for the symplectic inner product: for
an outer operator `h` without `Y` factors, pairing `G` with the promotion of
`h` is pairing the operator induced by `G` with `h`. -/
theorem symplecticInner_promoteOp (Xbar Zbar : NQubitPauliOperator n₁)
    (G : NQubitPauliOperator (n₁ * n₂)) {h : NQubitPauliOperator n₂}
    (hY : ∀ b, h b ≠ PauliOperator.Y) :
    symplecticInner G (promoteOp Xbar Zbar h) = symplecticInner (inducedOuterOp Xbar Zbar G) h := by
  rw [symplecticInner_eq_sum_restrictBlockOp]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [restrictBlockOp_promoteOp, symplecticInner_promoteSingle _ _ _ (hY b)]
  rfl

/-- If `Xbar` and `Zbar` anticommute, the operator induced by the promotion of
an outer operator `h` without `Y` factors is `h`. -/
lemma inducedOuterOp_promoteOp {Xbar Zbar : NQubitPauliOperator n₁}
    (hXZ : symplecticInner Xbar Zbar = 1) {h : NQubitPauliOperator n₂}
    (hY : ∀ b, h b ≠ PauliOperator.Y) :
    inducedOuterOp Xbar Zbar (promoteOp Xbar Zbar h) = h :=
  funext fun b => by
    rw [inducedOuterOp, restrictBlockOp_promoteOp, logicalClass_promoteSingle hXZ (hY b)]

/-- If `Xbar` and `Zbar` anticommute, promotion preserves the symplectic inner
product of outer operators without `Y` factors. -/
theorem symplecticInner_promoteOp_promoteOp {Xbar Zbar : NQubitPauliOperator n₁}
    (hXZ : symplecticInner Xbar Zbar = 1) {h₁ h₂ : NQubitPauliOperator n₂}
    (hY₁ : ∀ b, h₁ b ≠ PauliOperator.Y) (hY₂ : ∀ b, h₂ b ≠ PauliOperator.Y) :
    symplecticInner (promoteOp Xbar Zbar h₁) (promoteOp Xbar Zbar h₂) = symplecticInner h₁ h₂ := by
  rw [symplecticInner_promoteOp _ _ _ hY₂, inducedOuterOp_promoteOp hXZ hY₁]

/-- The identity operator induces the identity operator. -/
lemma inducedOuterOp_identity (Xbar Zbar : NQubitPauliOperator n₁) :
    inducedOuterOp Xbar Zbar (identity (n₁ * n₂)) = identity n₂ :=
  funext fun _ => logicalClass_eq_I_iff.mpr
    ⟨symplecticInner_identity_left _, symplecticInner_identity_left _⟩

/-- Up to phase, the induced outer operator is multiplicative. -/
lemma inducedOuterOp_mul (Xbar Zbar : NQubitPauliOperator n₁)
    (x y : NQubitPauliGroupElement (n₁ * n₂)) :
    inducedOuterOp Xbar Zbar (x * y).operators =
      (inducedOuterOp Xbar Zbar x.operators *ₚ inducedOuterOp Xbar Zbar y.operators).operators :=
  funext fun b => logicalClass_mul Xbar Zbar (restrictBlock b x) (restrictBlock b y)

/-! ## The data of a concatenation -/

/-- The data for concatenating an inner CSS code `Cin` with one logical qubit
and an outer CSS code `Cout`. Each code comes with a chosen logical basis and a
generator-list presentation whose generators are split into `Z`-type and
`X`-type ones. The inner logical operators `Cin.logicalX 0` and
`Cin.logicalZ 0` are an `X`-type and a `Z`-type element of phase `+1`, and the
outer logical operators are `X`-type and `Z`-type. -/
structure ConcatCSSData (n₁ n₂ k₂ : ℕ) where
  /-- The inner code, with its logical basis. -/
  Cin : StabilizerCodeWithLogicals n₁ 1
  /-- The outer code, with its logical basis. -/
  Cout : StabilizerCodeWithLogicals n₂ k₂
  /-- A generator-list presentation of the inner code. -/
  Pin : StabilizerCode.Presentation n₁ 1
  /-- A generator-list presentation of the outer code. -/
  Pout : StabilizerCode.Presentation n₂ k₂
  /-- `Pin` presents `Cin`: the inner stabilizer group is generated by the
  list of `Pin`. -/
  Cin_toSubgroup :
    Cin.toStabilizerGroup.toSubgroup = Subgroup.closure (listToSet Pin.generatorsList)
  /-- `Pout` presents `Cout`: the outer stabilizer group is generated by the
  list of `Pout`. -/
  Cout_toSubgroup :
    Cout.toStabilizerGroup.toSubgroup = Subgroup.closure (listToSet Pout.generatorsList)
  /-- The `Z`-type inner generators. -/
  innerZ : List (NQubitPauliGroupElement n₁)
  /-- The `X`-type inner generators. -/
  innerX : List (NQubitPauliGroupElement n₁)
  /-- The inner generators are the `Z`-type ones together with the `X`-type
  ones. -/
  inner_split : List.Perm Pin.generatorsList (innerZ ++ innerX)
  /-- The elements of `innerZ` are `Z`-type. -/
  innerZ_isZ : ∀ g ∈ innerZ, IsZTypeElement g
  /-- The elements of `innerX` are `X`-type. -/
  innerX_isX : ∀ g ∈ innerX, IsXTypeElement g
  /-- The `Z`-type outer generators. -/
  outerZ : List (NQubitPauliGroupElement n₂)
  /-- The `X`-type outer generators. -/
  outerX : List (NQubitPauliGroupElement n₂)
  /-- The outer generators are the `Z`-type ones together with the `X`-type
  ones. -/
  outer_split : List.Perm Pout.generatorsList (outerZ ++ outerX)
  /-- The elements of `outerZ` are `Z`-type. -/
  outerZ_isZ : ∀ g ∈ outerZ, IsZTypeElement g
  /-- The elements of `outerX` are `X`-type. -/
  outerX_isX : ∀ g ∈ outerX, IsXTypeElement g
  /-- The inner logical `X` operator is `X`-type. -/
  innerLogX_isX : NQubitPauliOperator.IsXType (Cin.logicalX 0).operators
  /-- The inner logical `X` operator has phase `+1`. -/
  innerLogX_phaseZero : (Cin.logicalX 0).phasePower = 0
  /-- The inner logical `Z` operator is `Z`-type. -/
  innerLogZ_isZ : NQubitPauliOperator.IsZType (Cin.logicalZ 0).operators
  /-- The inner logical `Z` operator has phase `+1`. -/
  innerLogZ_phaseZero : (Cin.logicalZ 0).phasePower = 0
  /-- The outer logical `X` operators are `X`-type; in particular they have no
  `Y` factor, so promotion is faithful on them. -/
  outerLogX_isX : ∀ ℓ : Fin k₂, NQubitPauliOperator.IsXType (Cout.logicalX ℓ).operators
  /-- The outer logical `Z` operators are `Z`-type. -/
  outerLogZ_isZ : ∀ ℓ : Fin k₂, NQubitPauliOperator.IsZType (Cout.logicalZ ℓ).operators

namespace ConcatCSSData

variable (D : ConcatCSSData n₁ n₂ k₂)

/-- The operator part of the inner logical `X`: the image of `X` under
promotion. -/
def Xbar : NQubitPauliOperator n₁ := (D.Cin.logicalX 0).operators

/-- The operator part of the inner logical `Z`: the image of `Z` under
promotion. -/
def Zbar : NQubitPauliOperator n₁ := (D.Cin.logicalZ 0).operators

/-- The element of phase `+1` with operator part `Xbar` is the inner logical
`X`. -/
lemma ofOperator_Xbar : ofOperator D.Xbar = D.Cin.logicalX 0 :=
  NQubitPauliGroupElement.ext _ _ D.innerLogX_phaseZero.symm rfl

/-- The element of phase `+1` with operator part `Zbar` is the inner logical
`Z`. -/
lemma ofOperator_Zbar : ofOperator D.Zbar = D.Cin.logicalZ 0 :=
  NQubitPauliGroupElement.ext _ _ D.innerLogZ_phaseZero.symm rfl

/-- The inner logical operators anticommute: their symplectic inner product is
`1`. -/
lemma symplecticInner_Xbar_Zbar : symplecticInner D.Xbar D.Zbar = 1 :=
  (anticommutes_iff_symplectic_inner_one _ _).mp (D.Cin.logicalOps 0).anticommute

/-- An inner generator lies in the inner stabilizer group. -/
lemma mem_Cin_of_mem_gens {g : NQubitPauliGroupElement n₁} (hg : g ∈ D.Pin.generatorsList) :
    g ∈ D.Cin.toStabilizerGroup.toSubgroup :=
  D.Cin_toSubgroup ▸ Subgroup.subset_closure hg

/-- An outer generator lies in the outer stabilizer group. -/
lemma mem_Cout_of_mem_gens {g : NQubitPauliGroupElement n₂} (hg : g ∈ D.Pout.generatorsList) :
    g ∈ D.Cout.toStabilizerGroup.toSubgroup :=
  D.Cout_toSubgroup ▸ Subgroup.subset_closure hg

/-- The outer generators have no `Y` factor: each is `Z`-type or `X`-type. -/
lemma outer_gen_noY {y : NQubitPauliGroupElement n₂} (hy : y ∈ D.outerZ ++ D.outerX)
    (b : Fin n₂) : y.operators b ≠ PauliOperator.Y := by
  rcases List.mem_append.mp hy with hz | hx
  · exact (D.outerZ_isZ y hz).2.ne_Y b
  · exact (D.outerX_isX y hx).2.ne_Y b

/-! ## The generator list of the concatenated code -/

/-- The inner generators, embedded in every block. -/
def s1PerBlockList : List (NQubitPauliGroupElement (n₁ * n₂)) :=
  (List.finRange n₂).flatMap (fun b => D.Pin.generatorsList.map (embedBlock b))

/-- The promoted outer generators, `Z`-type ones first. -/
def promotedOuterList : List (NQubitPauliGroupElement (n₁ * n₂)) :=
  (D.outerZ ++ D.outerX).map (promoteE D.Xbar D.Zbar)

/-- The generator list of the concatenated code: the inner generators embedded
in every block, followed by the promoted outer generators. -/
def concatGeneratorsList : List (NQubitPauliGroupElement (n₁ * n₂)) :=
  D.s1PerBlockList ++ D.promotedOuterList

/-- A concatenated generator is an inner generator embedded in a block or a
promoted outer generator. -/
lemma mem_concatGeneratorsList {x : NQubitPauliGroupElement (n₁ * n₂)} :
    x ∈ D.concatGeneratorsList ↔
      (∃ b, ∃ s ∈ D.Pin.generatorsList, embedBlock b s = x) ∨
        ∃ y ∈ D.outerZ ++ D.outerX, promoteE D.Xbar D.Zbar y = x := by
  simp only [concatGeneratorsList, s1PerBlockList, promotedOuterList, List.mem_append,
    List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]

/-- An inner generator embedded in a block is a concatenated generator. -/
lemma embedBlock_mem_concatGeneratorsList (b : Fin n₂) {s : NQubitPauliGroupElement n₁}
    (hs : s ∈ D.Pin.generatorsList) : embedBlock b s ∈ D.concatGeneratorsList :=
  D.mem_concatGeneratorsList.mpr (Or.inl ⟨b, s, hs, rfl⟩)

/-- A promoted outer generator is a concatenated generator. -/
lemma promoteE_mem_concatGeneratorsList {y : NQubitPauliGroupElement n₂}
    (hy : y ∈ D.outerZ ++ D.outerX) : promoteE D.Xbar D.Zbar y ∈ D.concatGeneratorsList :=
  D.mem_concatGeneratorsList.mpr (Or.inr ⟨y, hy, rfl⟩)

/-- There are `n₂ * (n₁ - 1)` embedded inner generators. -/
lemma s1PerBlockList_length : D.s1PerBlockList.length = n₂ * (n₁ - 1) := by
  simp [s1PerBlockList, List.length_flatMap, D.Pin.generators_length]

/-- There are `n₂ - k₂` promoted outer generators. -/
lemma promotedOuterList_length : D.promotedOuterList.length = n₂ - k₂ := by
  rw [promotedOuterList, List.length_map, ← D.outer_split.length_eq, D.Pout.generators_length]

/-- The concatenated code has `n₁ * n₂ - k₂` generators. -/
lemma concatGeneratorsList_length : D.concatGeneratorsList.length = n₁ * n₂ - k₂ := by
  rw [concatGeneratorsList, List.length_append, D.s1PerBlockList_length,
    D.promotedOuterList_length]
  have hn₁ : 1 ≤ n₁ := D.Cin.hk
  have hk₂ : k₂ ≤ n₂ := D.Cout.hk
  have h₁ : n₂ * (n₁ - 1) = n₁ * n₂ - n₂ := by rw [Nat.mul_sub, Nat.mul_one, Nat.mul_comm]
  have h₂ : n₂ ≤ n₁ * n₂ := Nat.le_mul_of_pos_left n₂ hn₁
  omega

/-- The concatenated generators have phase `+1`. -/
lemma concatGeneratorsList_phaseZero : AllPhaseZero D.concatGeneratorsList := by
  intro g hg
  obtain ⟨b, s, -, rfl⟩ | ⟨y, -, rfl⟩ := D.mem_concatGeneratorsList.mp hg <;> rfl

end ConcatCSSData

end Concatenation

end Quantum
