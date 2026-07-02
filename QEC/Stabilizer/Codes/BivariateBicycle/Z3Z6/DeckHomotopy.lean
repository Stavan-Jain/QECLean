/-
# The deck homotopy (R) for the [[72,4,8]] cover

`homotopyR : coverData.DeckTrivialOnH1` — the deck translation `σ = ·x³`
acts trivially on `H₁(cover)`.

The certificate is even simpler than gross's: a single weight-8 polynomial

  `p = x²(1 + y² + y⁴) + x³(1 + y⁴) + x⁴(1 + y²) + x⁵`

satisfies `p ⋆ B = 1 + x³` over `F₂[Z₆×Z₆]`, so the chain homotopy of
`deckTrivial_of_homotopy_certificate` is `C(v) = p ⋆ v_R` with the
`E ∘ ∂₁` correction `E(w) = (p ⋆ w | 0)`:

  left block:  `A⋆(p⋆v_R) + p⋆(B⋆v_L + A⋆v_R) = p⋆B⋆v_L = (1+x³)⋆v_L`,
  right block: `B⋆(p⋆v_R)                     = p⋆B⋆v_R = (1+x³)⋆v_R`.

(Compare gross's two-identity route `B⋆B = 1+x²+x⁴`,
`(1+x²)(1+x²+x⁴) = 1+x⁶` in `Codes/BivariateBicycle/DeckHomotopy.lean`.)
The `δ`-basis identity is one kernel computation; provenance of `p`:
`experiments/bb_lab/scripts/gen_pair72_z6z6_data.py` §3.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.Defs

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z3Z6

/-- The homotopy polynomial
`p = x²(1 + y² + y⁴) + x³(1 + y⁴) + x⁴(1 + y²) + x⁵`. -/
def pPoly : G72 → ZMod 2 := fun g =>
  if g = (2, 0) ∨ g = (2, 2) ∨ g = (2, 4) ∨ g = (3, 0) ∨
     g = (3, 4) ∨ g = (4, 0) ∨ g = (4, 2) ∨ g = (5, 0) then 1 else 0

/-- The homotopy 2-chain map `C(v) = p ⋆ v_R`. -/
def hC (v : G72 × Fin 2 → ZMod 2) : G72 → ZMod 2 :=
  conv pPoly (rightHalf v)

/-- The `∂₁`-correction `E(w) = (p ⋆ w | 0)`. -/
def hE (w : G72 → ZMod 2) : G72 × Fin 2 → ZMod 2 := fun q =>
  if q.2 = 0 then conv pPoly w q.1 else 0

lemma hC_zero : hC 0 = 0 := by
  funext g
  simp only [hC, conv_apply, rightHalf, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero]

lemma hC_add (a b : G72 × Fin 2 → ZMod 2) : hC (a + b) = hC a + hC b := by
  have hhalf : rightHalf (a + b) = rightHalf a + rightHalf b := rfl
  unfold hC
  rw [hhalf, conv_add_right]

lemma hE_zero : hE 0 = 0 := by
  funext q
  simp only [hE, conv_apply, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  split <;> rfl

lemma hE_add (a b : G72 → ZMod 2) : hE (a + b) = hE a + hE b := by
  funext q
  simp only [hE, Pi.add_apply]
  by_cases hq : q.2 = 0
  · rw [if_pos hq, if_pos hq, if_pos hq, conv_add_right]
    rfl
  · rw [if_neg hq, if_neg hq, if_neg hq, add_zero]

/-- The `δ`-basis chain-homotopy identity, by kernel computation. -/
theorem homotopy_basis : ∀ q : G72 × Fin 2,
    Pi.single q 1 + coverData.deckShift1 (Pi.single q 1)
        + hE (bbBoundary1Fn a72 b72 (Pi.single q 1))
      = bbBoundary2Fn a72 b72 (hC (Pi.single q 1)) := by
  native_decide

/-- **The deck homotopy (R)** for the `[[72,4,8]]` cover. -/
theorem homotopyR : coverData.DeckTrivialOnH1 :=
  coverData.deckTrivial_of_homotopy_certificate hC hE
    hC_zero hC_add hE_zero hE_add homotopy_basis

end Z3Z6
end BB
end Homological
end Stabilizer
end Quantum
