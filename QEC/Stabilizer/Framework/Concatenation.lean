import QEC.Stabilizer.Framework.Concatenation.Embedding
import QEC.Stabilizer.Framework.Concatenation.Promotion
import QEC.Stabilizer.Framework.Concatenation.Constructor
import QEC.Stabilizer.Framework.Concatenation.Restriction

/-!
# Framework.Concatenation

Infrastructure for **code concatenation** (Tiers 0–1b of the CSS concatenation
plan, `pipeline/attempts/concat_css_general/`).

Sub-modules:
- `QEC.Stabilizer.Framework.Concatenation.Embedding` (M1) — `qIdx` / `blockOf` /
  `posOf` block indexing and `embedBlock` (place an inner operator into one
  block), with weight, support, multiplicativity, and parity-commutation lemmas.
  Depends on `Foundations` only.
- `QEC.Stabilizer.Framework.Concatenation.Promotion` (M2) — the `I ↦ I`,
  `X ↦ X̄₁`, `Z ↦ Z̄₁` promotion map (`promoteE`), the `ConcatCSSData` input
  bundle, and the concatenated generator list with its length / phase-zero /
  CSS-typing lemmas. Sits at the `Framework.Symplectic` tier (uses
  `StabilizerCode`, the CSS predicates, and `AllPhaseZero`).
- `QEC.Stabilizer.Framework.Concatenation.Constructor` (M3) — the
  `concatenate : ConcatCSSData → StabilizerCode (n₁ * n₂) k₂` constructor.
  All obligation proofs discharged; `concatenate` is `sorry`-free.
- `QEC.Stabilizer.Framework.Concatenation.Restriction` (M5, part 1) — the
  block-restriction calculus `restrictBlock b g`, weight additivity
  (`weight_eq_sum_restrictBlock`), the anticommuting-count parity bridge, and
  `restrictBlock_mem_centralizer` (every block restriction of a centralizing
  element centralizes the inner stabilizer).
-/
