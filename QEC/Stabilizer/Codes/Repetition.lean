import QEC.Stabilizer.Codes.Repetition.Three
import QEC.Stabilizer.Codes.Repetition.ThreeLogicals
import QEC.Stabilizer.Codes.Repetition.N
import QEC.Stabilizer.Codes.Repetition.NLogicals

/-!
# Repetition codes

The classical bit-flip repetition codes as quantum stabilizer codes of
distance 1, in the two-file layout described in `Codes/_TEMPLATE.lean`.

- `Three`: the 3-qubit repetition code `[[3, 1, 1]]`, from its two `ZZ` checks
  to `RepetitionCode3.stabilizerCodeWithDistance`.
- `ThreeLogicals`: its logical basis `X̄ = XXX`, `Z̄ = ZZZ`, ending in
  `RepetitionCode3.stabilizerCodeWithLogicals`.
- `N`: the family `[[n+2, 1, 1]]` on `n + 2` qubits, from its `n + 1` adjacent
  `ZZ` checks to `RepetitionCodeN.stabilizerCodeWithDistance`.
- `NLogicals`: its logical basis `X̄ = X⊗ⁿ⁺²`, `Z̄ = Z⊗ⁿ⁺²` for odd `n + 2`,
  ending in `RepetitionCodeN.stabilizerCodeWithLogicals`.
-/
