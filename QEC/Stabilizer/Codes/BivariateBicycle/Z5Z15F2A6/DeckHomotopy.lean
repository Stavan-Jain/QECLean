/-
# The deck homotopy (R) for the [[300,8,16]] cover

`homotopyR : coverData.DeckTrivialOnH1` — the deck translation `σ = ·y¹⁵`
acts trivially on `H₁(cover)`.

Via the A12 Bezout route (`deckTrivial_of_bezout`): the pair

  `P` (25 monomials), `Q = y⁹ + y¹⁵ + y¹⁶`

satisfies the Bezout identity `P⋆A + Q⋆B = 1 + y¹⁵` over `F₂[Z₅×Z₃₀]`,
which yields the chain homotopy `1 + σ = ∂₂∘C + E∘∂₁` with module maps
`C v = P⋆v_L + Q⋆v_R`, `E h = (Q⋆h | P⋆h)`.  The finite check is one
`G300`-indexed kernel identity (150 points).  By A12 such a witness
exists iff `k(cover) = k(base)` (8 = 8 here); provenance of `(P, Q)`
(greedy-sparsified linear solve):
`experiments/bb_lab/scripts/gen_f2a6_z5z30_data.py` §2.

(Compare the two `P = 0` instances: gross's `(1+x²)⋆B⋆B = 1+x⁶` and
pair72's `p⋆B = 1+x³`.  Here a genuinely two-sided witness is used —
the sparsified solution touches both `A` and `B`.)
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.Defs

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z5Z15F2A6

/-- The Bezout polynomial `P` (25 monomials). -/
def pPoly : G300 → ZMod 2 := fun g =>
  if g = (0, 24) ∨ g = (0, 25) ∨ g = (0, 26) ∨ g = (0, 27) ∨
     g = (0, 28) ∨ g = (0, 29) ∨ g = (1, 15) ∨ g = (1, 16) ∨
     g = (1, 17) ∨ g = (1, 18) ∨ g = (1, 21) ∨ g = (1, 24) ∨
     g = (1, 25) ∨ g = (1, 26) ∨ g = (1, 28) ∨ g = (2, 15) ∨
     g = (2, 17) ∨ g = (2, 24) ∨ g = (2, 26) ∨ g = (3, 15) ∨
     g = (3, 16) ∨ g = (3, 24) ∨ g = (3, 25) ∨ g = (4, 15) ∨
     g = (4, 24) then 1 else 0

/-- The Bezout polynomial `Q = y⁹ + y¹⁵ + y¹⁶`. -/
def qPoly : G300 → ZMod 2 := fun g =>
  if g = (0, 9) ∨ g = (0, 15) ∨ g = (0, 16) then 1 else 0

/-- The Bezout witness `P⋆A + Q⋆B = 1 + y¹⁵` over `F₂[Z₅×Z₃₀]`. -/
theorem pq_bezout :
    conv pPoly coverData.Ac + conv qPoly coverData.Bc
      = coverData.deckPoly := by
  native_decide

/-- **The deck homotopy (R)** for the `[[300,8,16]]` cover. -/
theorem homotopyR : coverData.DeckTrivialOnH1 :=
  coverData.deckTrivial_of_bezout pPoly qPoly pq_bezout

end Z5Z15F2A6
end BB
end Homological
end Stabilizer
end Quantum
