import QEC.Stabilizer.Framework.Concatenation.Constructor

/-!
# Concatenation: the induced outer logical operator

A logical operator `g` of the concatenated code induces a logical operator
`inducedOuter D g` of the outer code: its factor at block `b` is the logical
class of the restriction of `g` to block `b`, that is, the single-qubit Pauli
that the restriction acts as on the logical qubit of the inner code.

- `restrictBlock_mem_centralizer`: the block restrictions of an element of the
  centralizer of the concatenated stabilizer group lie in the centralizer of
  the inner stabilizer group.
- `inducedOuter_commute_iff`: `inducedOuter D g` commutes with an outer element
  `h` without `Y` factors iff `g` commutes with the promotion of `h`. Hence
  `inducedOuter_mem_centralizer`.
- `mem_support_inducedOuter_iff`: block `b` is in the support of
  `inducedOuter D g` iff the restriction of `g` to block `b` is a nontrivial
  logical operator of the inner code.
- `inducedOuter_coset_injective`: if `inducedOuter D g` has the operator part of
  an outer stabilizer element, then `g` has the operator part of a concatenated
  stabilizer element.
- `inducedOuter_isNontrivialLogical`: if `g` is a nontrivial logical operator of
  the concatenated code, then `inducedOuter D g` is a nontrivial logical
  operator of the outer code.
-/

namespace Quantum.Concatenation

open NQubitPauliGroupElement NQubitPauliOperator StabilizerGroup

variable {n₁ n₂ k₂ : ℕ}

/-- The outer Pauli group element of phase `+1` induced by `g`: its factor at
block `b` is the logical class, relative to the inner logical operators, of the
restriction of `g` to block `b`. -/
def inducedOuter (D : ConcatCSSData n₁ n₂ k₂) (g : NQubitPauliGroupElement (n₁ * n₂)) :
    NQubitPauliGroupElement n₂ :=
  ofOperator (inducedOuterOp D.Xbar D.Zbar g.operators)

@[simp] lemma inducedOuter_operators (D : ConcatCSSData n₁ n₂ k₂)
    (g : NQubitPauliGroupElement (n₁ * n₂)) :
    (inducedOuter D g).operators = inducedOuterOp D.Xbar D.Zbar g.operators := rfl

namespace ConcatCSSData

variable (D : ConcatCSSData n₁ n₂ k₂)

/-! ## The induced outer operator is a logical operator -/

/-- If `g` commutes with the concatenated stabilizer group, each of its block
restrictions commutes with the inner stabilizer group. -/
lemma restrictBlock_mem_centralizer (g : NQubitPauliGroupElement (n₁ * n₂))
    (hg : g ∈ centralizer D.concatStabGroup) (b : Fin n₂) :
    restrictBlock b g ∈ centralizer D.Cin.toStabilizerGroup :=
  (mem_centralizer_iff_closure _ _ _ D.Cin_toSubgroup).mpr fun s hs =>
    ((restrictBlock_commute_embed_iff b g s).mp
      ((mem_centralizer_iff g _).mp hg _ (D.embedBlock_mem_concatStabGroup b hs)).symm).symm

/-- For an outer element `h` without `Y` factors, the induced outer operator of
`g` commutes with `h` iff `g` commutes with the promotion of `h`. -/
theorem inducedOuter_commute_iff (g : NQubitPauliGroupElement (n₁ * n₂))
    {h : NQubitPauliGroupElement n₂} (hY : ∀ b, h.operators b ≠ PauliOperator.Y) :
    inducedOuter D g * h = h * inducedOuter D g ↔
      g * promoteE D.Xbar D.Zbar h = promoteE D.Xbar D.Zbar h * g := by
  rw [commutes_iff_symplectic_inner_zero, commutes_iff_symplectic_inner_zero, promoteE_operators,
    symplecticInner_promoteOp _ _ _ hY, inducedOuter_operators]

/-- If `g` commutes with the concatenated stabilizer group, its induced outer
operator commutes with the outer stabilizer group. -/
theorem inducedOuter_mem_centralizer (g : NQubitPauliGroupElement (n₁ * n₂))
    (hg : g ∈ centralizer D.concatStabGroup) :
    inducedOuter D g ∈ centralizer D.Cout.toStabilizerGroup := by
  refine (mem_centralizer_iff_closure _ _ _ D.Cout_toSubgroup).mpr fun y hy => ?_
  have hy' : y ∈ D.outerZ ++ D.outerX := D.outer_split.mem_iff.mp hy
  exact ((D.inducedOuter_commute_iff g (D.outer_gen_noY hy')).mpr
    ((mem_centralizer_iff g _).mp hg _ (D.promoteE_mem_concatStabGroup hy')).symm).symm

/-! ## The support of the induced outer operator -/

/-- For `g` in the centralizer of the concatenated stabilizer group, the
induced outer operator is `I` at block `b` iff the restriction of `g` to block
`b` has the operator part of an inner stabilizer element. -/
lemma inducedOuterOp_eq_I_iff (g : NQubitPauliGroupElement (n₁ * n₂))
    (hg : g ∈ centralizer D.concatStabGroup) (b : Fin n₂) :
    inducedOuterOp D.Xbar D.Zbar g.operators b = PauliOperator.I ↔
      ∃ s ∈ D.Cin.toStabilizerGroup.toSubgroup, s.operators = restrictBlockOp b g.operators := by
  refine ⟨fun h => ?_, fun ⟨s, hs, hsop⟩ => ?_⟩
  · obtain ⟨hX, hZ⟩ := (D.logicalClass_eq_I_iff_commute (restrictBlock b g)).mp h
    exact operators_eq_stab_of_commutes_both_logicals D.Cin _
      (D.restrictBlock_mem_centralizer g hg b) hX hZ
  · exact (congrArg (logicalClass D.Xbar D.Zbar) hsop).symm.trans (D.logicalClass_of_mem_Cin hs)

/-- For `g` in the centralizer of the concatenated stabilizer group, block `b`
is in the support of the induced outer operator iff the restriction of `g` to
block `b` is a nontrivial logical operator of the inner code. -/
theorem mem_support_inducedOuter_iff (g : NQubitPauliGroupElement (n₁ * n₂))
    (hg : g ∈ centralizer D.concatStabGroup) (b : Fin n₂) :
    b ∈ (inducedOuter D g).support ↔
      IsNontrivialLogicalOperator (restrictBlock b g) D.Cin.toStabilizerGroup := by
  rw [NQubitPauliGroupElement.mem_support, inducedOuter_operators, ne_eq,
    D.inducedOuterOp_eq_I_iff g hg b, IsNontrivialLogicalOperator_iff,
    and_iff_right (D.restrictBlock_mem_centralizer g hg b)]
  exact not_exists.trans (forall_congr' fun s => not_and)

/-! ## Nontrivial logical operators induce nontrivial logical operators -/

/-- The symplectic vector of an inner stabilizer element embedded in a block
lies in the span of the check-matrix rows of the concatenated generators. -/
lemma toSymplectic_embedBlockOp_mem_sympSpan (b : Fin n₂) {s : NQubitPauliGroupElement n₁}
    (hs : s ∈ D.Cin.toStabilizerGroup.toSubgroup) :
    toSymplectic (embedBlockOp b s.operators) ∈ sympSpan D.concatGeneratorsList := by
  rw [D.Cin_toSubgroup] at hs
  induction hs using Subgroup.closure_induction with
  | mem c hc =>
    exact toSymplectic_mem_sympSpan_of_mem (D.embedBlock_mem_concatGeneratorsList b hc)
  | one =>
    have h : toSymplectic (embedBlockOp b (1 : NQubitPauliGroupElement n₁).operators) = 0 :=
      (congrArg toSymplectic (embedBlockOp_identity b)).trans toSymplectic_one_operators
    rw [h]
    exact zero_mem _
  | mul x y _ _ hx hy =>
    have h : toSymplectic (embedBlockOp b (x * y).operators) =
        toSymplectic (embedBlockOp b x.operators) + toSymplectic (embedBlockOp b y.operators) :=
      (congrArg toSymplectic (mulOp_embedBlockOp_operators b x.operators y.operators).symm).trans
        (funext (toSymplectic_add _ _))
    rw [h]
    exact add_mem hx hy
  | inv x _ hx => exact hx

/-- Every outer stabilizer element is, up to phase, induced by a concatenated
stabilizer element: a product of outer generators is induced by the product of
their promotions. -/
lemma exists_mem_concatStabGroup_inducedOuterOp {t : NQubitPauliGroupElement n₂}
    (ht : t ∈ D.Cout.toStabilizerGroup.toSubgroup) :
    ∃ u ∈ D.concatStabGroup.toSubgroup,
      inducedOuterOp D.Xbar D.Zbar u.operators = t.operators := by
  rw [D.Cout_toSubgroup] at ht
  induction ht using Subgroup.closure_induction with
  | mem y hy =>
    have hy' : y ∈ D.outerZ ++ D.outerX := D.outer_split.mem_iff.mp hy
    exact ⟨_, D.promoteE_mem_concatStabGroup hy',
      inducedOuterOp_promoteOp D.symplecticInner_Xbar_Zbar (D.outer_gen_noY hy')⟩
  | one => exact ⟨1, Subgroup.one_mem _, inducedOuterOp_identity _ _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨u, hu, hux⟩ := hx
    obtain ⟨v, hv, hvy⟩ := hy
    exact ⟨u * v, Subgroup.mul_mem _ hu hv, (inducedOuterOp_mul _ _ u v).trans
      (congrArg₂ (fun P Q => (P *ₚ Q).operators) hux hvy)⟩
  | inv x _ hx =>
    obtain ⟨u, hu, hux⟩ := hx
    exact ⟨u⁻¹, Subgroup.inv_mem _ hu, hux⟩

/-- If the induced outer operator of a centralizer element `g` has the operator
part of an outer stabilizer element `t`, then `g` has the operator part of a
concatenated stabilizer element.

Take a concatenated stabilizer element `u` inducing `t`. Then `g * u` induces
the identity, so each of its block restrictions has the operator part of an
inner stabilizer element, and `g * u` is a product of embedded inner stabilizer
elements up to phase. -/
theorem inducedOuter_coset_injective (g : NQubitPauliGroupElement (n₁ * n₂))
    (hg : g ∈ centralizer D.concatStabGroup)
    (t : NQubitPauliGroupElement n₂) (ht : t ∈ D.Cout.toStabilizerGroup.toSubgroup)
    (htop : t.operators = (inducedOuter D g).operators) :
    ∃ s ∈ D.concatStabGroup.toSubgroup, s.operators = g.operators := by
  obtain ⟨u, hu, hut⟩ := D.exists_mem_concatStabGroup_inducedOuterOp ht
  have hgu : g * u ∈ centralizer D.concatStabGroup :=
    Subgroup.mul_mem _ hg (stabilizer_le_centralizer _ hu)
  have hI : inducedOuterOp D.Xbar D.Zbar (g * u).operators = identity n₂ := by
    rw [inducedOuterOp_mul, hut, ← inducedOuter_operators, ← htop, mulOp_self, one_operators_def]
  have hspan : toSymplectic (g * u).operators ∈ sympSpan D.concatGeneratorsList := by
    rw [toSymplectic_eq_sum_embedBlockOp_restrictBlockOp]
    refine Submodule.sum_mem _ fun b _ => ?_
    obtain ⟨s, hs, hsop⟩ := (D.inducedOuterOp_eq_I_iff (g * u) hgu b).mp (congrFun hI b)
    rw [← hsop]
    exact D.toSymplectic_embedBlockOp_mem_sympSpan b hs
  have h : toSymplectic g.operators =
      toSymplectic (g * u).operators + toSymplectic u.operators := by
    funext j
    rw [Pi.add_apply, toSymplectic_mul g u j, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  refine exists_mem_closure_of_symp_in_span D.concatGeneratorsList g.operators ?_
  rw [h]
  exact add_mem hspan (mem_closure_implies_symp_in_span _ u hu)

/-- The induced outer operator of a nontrivial logical operator of the
concatenated code is a nontrivial logical operator of the outer code. -/
theorem inducedOuter_isNontrivialLogical (g : NQubitPauliGroupElement (n₁ * n₂))
    (hg : IsNontrivialLogicalOperator g D.concatStabGroup) :
    IsNontrivialLogicalOperator (inducedOuter D g) D.Cout.toStabilizerGroup :=
  (IsNontrivialLogicalOperator_iff _ _).mpr ⟨D.inducedOuter_mem_centralizer g hg.1,
    fun t ht htop =>
      let ⟨s, hs, hsop⟩ := D.inducedOuter_coset_injective g hg.1 t ht htop
      hg.2 s hs hsop⟩

/-- The induced outer operator of a nontrivial logical operator of the
concatenated code is not in the outer stabilizer group. -/
theorem inducedOuter_not_mem_stabilizer (g : NQubitPauliGroupElement (n₁ * n₂))
    (hg : IsNontrivialLogicalOperator g D.concatStabGroup) :
    inducedOuter D g ∉ D.Cout.toStabilizerGroup.toSubgroup :=
  RepresentsNontrivialCoset.not_mem (D.inducedOuter_isNontrivialLogical g hg)

end ConcatCSSData

end Quantum.Concatenation
