import QEC.Stabilizer.Framework.Concatenation.Embedding

/-!
# Framework.Concatenation

Operator-level infrastructure for **code concatenation** (milestone M1 of the
CSS concatenation plan, `pipeline/attempts/concat_css_general/`).

Depends on `Foundations` only — these are pure index + Pauli-operator algebra,
with no dependency on the `StabilizerCode` layer, so they sit at the Framework
tier and are reusable by the `Codes.Concat.*` constructor/distance modules.

Sub-modules:
- `QEC.Stabilizer.Framework.Concatenation.Embedding` — `qIdx` / `blockOf` /
  `posOf` block indexing and `embedBlock` (place an inner operator into one
  block), with weight, support, multiplicativity, and parity-commutation lemmas.
-/
