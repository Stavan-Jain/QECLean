import QEC.Stabilizer.Framework.Concatenation.Correspondence
import QEC.Stabilizer.Framework.Core.Logical.CodeDistance

/-!
# Concatenation: the distance of the concatenated code

Concatenating an inner code of distance `d₁` with an outer code of distance
`d₂` gives a code of distance at least `d₁ * d₂`.

- `ConcatCSSData.weight_ge_d1_mul_d2`: every nontrivial logical operator `g` of
  the concatenated code has weight at least `d₁ * d₂`. Its induced outer
  operator is a nontrivial logical operator of the outer code, so its support
  has at least `d₂` blocks; on each of these blocks the restriction of `g` is a
  nontrivial logical operator of the inner code, so it has weight at least
  `d₁`.
- `ConcatCSSData.exists_nontrivial_logical_weight_mul`: promoting an `X`-type
  outer logical operator `h` along a representative `x` of the inner logical
  `X` gives a nontrivial logical operator of weight `weight x * weight h`.
- `ConcatCSSData.concat_hasCodeDistance`: the concatenated code has distance
  `d₁ * d₂`, given a nontrivial logical operator of weight `d₁ * d₂`, and
  `ConcatCSSData.concat_hasCodeDistance_of_minWeight`: it is enough to give a
  representative of the inner logical `X` of weight `d₁` and an `X`-type outer
  logical operator of weight `d₂`.
- `ConcatCSSData.concatenateWithDistance`: the concatenated code as a
  `StabilizerCodeWithDistance (n₁ * n₂) k₂ (d₁ * d₂)`.
-/

namespace Quantum

namespace Concatenation.ConcatCSSData

open NQubitPauliGroupElement NQubitPauliOperator StabilizerGroup

variable {n₁ n₂ k₂ : ℕ} (D : ConcatCSSData n₁ n₂ k₂)

/-- Every nontrivial logical operator of the concatenated code has weight at
least `d₁ * d₂`, where `d₁` and `d₂` are the distances of the inner and the
outer code. -/
theorem weight_ge_d1_mul_d2 {d₁ d₂ : ℕ} (h1 : HasCodeDistance D.Cin.toStabilizerCode d₁)
    (h2 : HasCodeDistance D.Cout.toStabilizerCode d₂)
    (g : NQubitPauliGroupElement (n₁ * n₂))
    (hg : IsNontrivialLogicalOperator g D.concatStabGroup) :
    d₁ * d₂ ≤ weight g := by
  have hO := D.inducedOuter_isNontrivialLogical g hg
  calc d₁ * d₂ ≤ d₁ * (inducedOuter D g).support.card :=
        Nat.mul_le_mul_left d₁ (h2.min_weight _ d₂ _ hO hO.weight_pos)
    _ ≤ weight g := weight_ge_of_blocks_ge d₁ g _ fun b hb =>
        have hb' := (D.mem_support_inducedOuter_iff g hg.1 b).mp hb
        h1.min_weight _ d₁ _ hb' hb'.weight_pos

/-- Promoting an `X`-type outer logical operator `h` along a representative `x`
of the inner logical `X` gives a nontrivial logical operator of the
concatenated code of weight `weight x * weight h`.

Here `x` is an element of the inner centralizer that commutes with the inner
logical `X` and anticommutes with the inner logical `Z`, and `h` is an
`X`-type element of the outer centralizer that anticommutes with some outer
logical `Z`. The promotion of `h` along `x` is `x` on each block of the support
of `h`; it anticommutes with the promoted outer logical `Z`. -/
theorem exists_nontrivial_logical_weight_mul
    {x : NQubitPauliGroupElement n₁} (hx : x ∈ centralizer D.Cin.toStabilizerGroup)
    (hxX : x * D.Cin.logicalX 0 = D.Cin.logicalX 0 * x)
    (hxZ : Anticommute x (D.Cin.logicalZ 0))
    {h : NQubitPauliGroupElement n₂} (hh : h ∈ centralizer D.Cout.toStabilizerGroup)
    (hhX : IsXType h.operators) {ℓ : Fin k₂} (hhZ : Anticommute h (D.Cout.logicalZ ℓ)) :
    ∃ g, IsNontrivialLogicalOperator g D.concatStabGroup ∧ weight g = weight x * weight h := by
  have hcls := (D.logicalClass_eq_X_iff_commute x).mpr ⟨hxX, hxZ⟩
  refine ⟨promoteE x.operators D.Zbar h,
    isNontrivialLogicalOperator_of_anticommute_centralizer _
      (D.promoteE_rep_mem_centralizer hx hcls hhX hh) (D.concatLogicalZ_mem_centralizer ℓ) ?_,
    weight_promoteE_of_isXType _ _ hhX⟩
  rw [anticommutes_iff_symplectic_inner_one, concatLogicalZ, promoteE_operators,
    promoteE_operators, symplecticInner_promoteOp _ _ _ (D.outerLogZ_isZ ℓ).ne_Y,
    inducedOuterOp_promoteOp_of_isXType hcls hhX]
  exact (anticommutes_iff_symplectic_inner_one _ _).mp hhZ

/-- The concatenated code has distance `d₁ * d₂`, given a nontrivial logical
operator of weight `d₁ * d₂`; the lower bound is `weight_ge_d1_mul_d2`. -/
theorem concat_hasCodeDistance
    {d₁ d₂ : ℕ} (h1 : HasCodeDistance D.Cin.toStabilizerCode d₁)
    (h2 : HasCodeDistance D.Cout.toStabilizerCode d₂)
    (hwit : ∃ g, IsNontrivialLogicalOperator g D.concatStabGroup ∧ weight g = d₁ * d₂) :
    HasCodeDistance D.concatenate (d₁ * d₂) :=
  ⟨Nat.mul_pos h1.1 h2.1, fun g hg _ => D.weight_ge_d1_mul_d2 h1 h2 g hg, hwit⟩

/-- The concatenated code has distance `d₁ * d₂`, given a representative `x` of
the inner logical `X` of weight `d₁` and an `X`-type outer logical operator `h`
of weight `d₂`: the hypotheses of `exists_nontrivial_logical_weight_mul`,
which provides the nontrivial logical operator of weight `d₁ * d₂`. -/
theorem concat_hasCodeDistance_of_minWeight
    {d₁ d₂ : ℕ} (h1 : HasCodeDistance D.Cin.toStabilizerCode d₁)
    (h2 : HasCodeDistance D.Cout.toStabilizerCode d₂)
    {x : NQubitPauliGroupElement n₁} (hx : x ∈ centralizer D.Cin.toStabilizerGroup)
    (hxX : x * D.Cin.logicalX 0 = D.Cin.logicalX 0 * x)
    (hxZ : Anticommute x (D.Cin.logicalZ 0)) (hxw : weight x = d₁)
    {h : NQubitPauliGroupElement n₂} (hh : h ∈ centralizer D.Cout.toStabilizerGroup)
    (hhX : IsXType h.operators) {ℓ : Fin k₂} (hhZ : Anticommute h (D.Cout.logicalZ ℓ))
    (hhw : weight h = d₂) :
    HasCodeDistance D.concatenate (d₁ * d₂) :=
  D.concat_hasCodeDistance h1 h2
    (hxw ▸ hhw ▸ D.exists_nontrivial_logical_weight_mul hx hxX hxZ hh hhX hhZ)

/-- The concatenated code together with its distance `d₁ * d₂`. -/
noncomputable def concatenateWithDistance
    {d₁ d₂ : ℕ} (h1 : HasCodeDistance D.Cin.toStabilizerCode d₁)
    (h2 : HasCodeDistance D.Cout.toStabilizerCode d₂)
    (hwit : ∃ g, IsNontrivialLogicalOperator g D.concatStabGroup ∧ weight g = d₁ * d₂) :
    StabilizerCodeWithDistance (n₁ * n₂) k₂ (d₁ * d₂) where
  toStabilizerCode := D.concatenate
  hasDistance := D.concat_hasCodeDistance h1 h2 hwit

end Concatenation.ConcatCSSData

end Quantum
