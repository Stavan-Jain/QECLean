/-
# The deck homotopy (R) for the [[72,4,8]] cover

`homotopyR : coverData.DeckTrivialOnH1` — the deck translation `σ = ·x³`
acts trivially on `H₁(cover)`.

Via the A12 Bezout route (`deckTrivial_of_bezout`): the single weight-8
polynomial

  `p = x²(1 + y² + y⁴) + x³(1 + y⁴) + x⁴(1 + y²) + x⁵`

satisfies the Bezout identity `0 ⋆ A + p ⋆ B = 1 + x³` over `F₂[Z₆×Z₆]`,
which by `XDoubleCoverData.deckTrivial_of_bezout` (the `P = 0`, `Q = p`
case) yields the chain homotopy `1 + σ = ∂₂∘C + E∘∂₁` with module maps
`C v = p⋆v_R`, `E h = (p⋆h | 0)`.  The finite check is one `G72`-indexed
kernel identity (36 points), replacing the previous 72-point `δ`-basis
sweep of function equalities.  By A12 such a witness exists iff
`k(cover) = k(base)` (4 = 4 here); provenance of `p`:
`qec-lab:experiments/bb_lab/scripts/gen_pair72_z6z6_data.py` §3.

(Compare gross's two-identity route `B⋆B = 1+x²+x⁴`,
`(1+x²)(1+x²+x⁴) = 1+x⁶` in `Codes/BivariateBicycle/DeckHomotopy.lean` —
also a `P = 0` Bezout witness, with `Q = (1+x²)⋆B`.)
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

/-- The Bezout witness `0 ⋆ A + p ⋆ B = 1 + x³` over `F₂[Z₆×Z₆]`. -/
theorem pPoly_bezout :
    conv (0 : G72 → ZMod 2) coverData.Ac + conv pPoly coverData.Bc
      = coverData.deckPoly := by
  decide

/-- **The deck homotopy (R)** for the `[[72,4,8]]` cover. -/
theorem homotopyR : coverData.DeckTrivialOnH1 :=
  coverData.deckTrivial_of_bezout 0 pPoly pPoly_bezout

end Z3Z6
end BB
end Homological
end Stabilizer
end Quantum
