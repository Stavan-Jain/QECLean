/-
# The gross seam-coset Brouwer–Zimmermann walks

The two kernel walks of the gross certificate (`SeamBZ.lean`): every XOR of at
most five rows of `window₁` and at most four rows of `window₂` — `510 414` words
of the tagged coset code `seamC (ker ∂₂) + im ∂₂` — satisfies `okGross`: it is
zero, has weight `≥ 11`, or is an untagged word (a boundary) on the list of the
252 light boundaries.

`xor_walk_decide₂` splits each walk into one `decide +kernel` per pair of
first-chosen rows, so each kernel check (and its cache) stays small.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Gross.SeamBZData
import QEC.Stabilizer.Framework.Homological.BZCertificate

namespace Quantum.Stabilizer.Homological.BB.GrossBZ

open F2Mask

/-- The predicate the walks check: the word is zero, weighs at least `11` (its
low 72 bits, by the byte-table popcount), or is untagged and a listed light
boundary. Raw `Nat.*` functions keep the kernel off the notation's instances. -/
def okGross (X : ℕ) : Bool :=
  (Nat.beq X 0 || Nat.ble 11 (bitCountFast 9 X))
    || (Nat.beq (Nat.shiftRight X 72) 0 && lightMasks.contains X)

set_option maxHeartbeats 1000000 in
-- one declaration elaborates ~630 per-chunk `decide +kernel` auxiliary lemmas
/-- The first window's walk: every XOR of at most five of its rows. -/
theorem walk₁ : xorWalk okGross window₁Rows 5 0 = true := by
  unfold window₁Rows
  xor_walk_decide₂

/-- The second window's walk: every XOR of at most four of its rows. -/
theorem walk₂ : xorWalk okGross window₂Rows 4 0 = true := by
  unfold window₂Rows
  xor_walk_decide₂

end Quantum.Stabilizer.Homological.BB.GrossBZ
