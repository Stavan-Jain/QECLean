import QEC.Stabilizer.Codes.Iceberg.N
import QEC.Stabilizer.Codes.Iceberg.NLogicals

/-!
# Iceberg codes

The iceberg (generalized parity) codes `[[2m, 2m − 2, 2]]` for `m ≥ 2`, in the
two-file layout described in `Codes/_TEMPLATE.lean`.

- `N`: the family from its two generators `Z⊗²ᵐ`, `X⊗²ᵐ` to the code with its
  distance, `Iceberg.stabilizerCodeWithDistance`.
- `NLogicals`: the logical basis `X̄ᵢ = XᵢX₂ₘ₋₁`, `Z̄ᵢ = ZᵢZ₂ₘ₋₂`, ending in
  `Iceberg.stabilizerCodeWithLogicals`.
-/
