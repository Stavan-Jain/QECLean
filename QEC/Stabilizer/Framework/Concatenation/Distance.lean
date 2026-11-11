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
- `ConcatCSSData.concat_hasCodeDistance`: the concatenated code has distance
  `d₁ * d₂`, given a nontrivial logical operator of weight `d₁ * d₂`.
- `ConcatCSSData.concatenateWithDistance`: the concatenated code as a
  `StabilizerCodeWithDistance (n₁ * n₂) k₂ (d₁ * d₂)`.
-/

namespace Quantum

namespace Concatenation.ConcatCSSData

open NQubitPauliGroupElement StabilizerGroup

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

/-- The concatenated code has distance `d₁ * d₂`, given a nontrivial logical
operator of weight `d₁ * d₂`; the lower bound is `weight_ge_d1_mul_d2`. -/
theorem concat_hasCodeDistance
    (hindep : rowsLinearIndependent D.concatGeneratorsList)
    {d₁ d₂ : ℕ} (h1 : HasCodeDistance D.Cin.toStabilizerCode d₁)
    (h2 : HasCodeDistance D.Cout.toStabilizerCode d₂)
    (hwit : ∃ g, IsNontrivialLogicalOperator g D.concatStabGroup ∧ weight g = d₁ * d₂) :
    HasCodeDistance (D.concatenate hindep) (d₁ * d₂) :=
  ⟨Nat.mul_pos h1.1 h2.1, fun g hg _ => D.weight_ge_d1_mul_d2 h1 h2 g hg, hwit⟩

/-- The concatenated code together with its distance `d₁ * d₂`. -/
noncomputable def concatenateWithDistance
    (hindep : rowsLinearIndependent D.concatGeneratorsList)
    {d₁ d₂ : ℕ} (h1 : HasCodeDistance D.Cin.toStabilizerCode d₁)
    (h2 : HasCodeDistance D.Cout.toStabilizerCode d₂)
    (hwit : ∃ g, IsNontrivialLogicalOperator g D.concatStabGroup ∧ weight g = d₁ * d₂) :
    StabilizerCodeWithDistance (n₁ * n₂) k₂ (d₁ * d₂) where
  toStabilizerCode := D.concatenate hindep
  hasDistance := D.concat_hasCodeDistance hindep h1 h2 hwit

end Concatenation.ConcatCSSData

end Quantum
