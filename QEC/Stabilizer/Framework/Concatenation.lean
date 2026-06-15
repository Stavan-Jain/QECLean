import QEC.Stabilizer.Framework.Concatenation.Embedding
import QEC.Stabilizer.Framework.Concatenation.Promotion

/-!
# Framework.Concatenation

Infrastructure for **code concatenation** (Tiers 0–1a of the CSS concatenation
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
-/
