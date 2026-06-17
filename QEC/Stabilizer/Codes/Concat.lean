import QEC.Stabilizer.Codes.Concat.SteaneSteane
import QEC.Stabilizer.Codes.Concat.SteaneFourQubit

/-!
# Concatenated codes

Concrete instances of the CSS concatenation framework
(`Framework/Concatenation`, milestones M1–M6).

- `Codes.Concat.SteaneSteane` (M7) — Steane ⊗ Steane: the unconditional `[[49, 1, 9]]` code
  (`steaneConcat_hasCodeDistance_nine`), `k₂ = 1`.
- `Codes.Concat.SteaneFourQubit` — Steane ⊗ `[[4,2,2]]`: the unconditional `[[28, 2, 6]]` code
  (`steane422_hasCodeDistance_six`), exercising the `k₂ = 2` (multi-logical-qubit) path.
-/
