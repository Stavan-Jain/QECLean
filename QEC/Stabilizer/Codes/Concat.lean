import QEC.Stabilizer.Codes.Concat.SteaneSteane

/-!
# Concatenated codes

Concrete instances of the concatenation of CSS codes of
`Framework/Concatenation`.

- `SteaneSteane`: the Steane code concatenated with itself, `[[49, 1, 9]]`,
  ending in `SteaneSteane.stabilizerCodeWithDistance`. Its distance is derived
  from the distance and the weight-3 logical operator of the seven-qubit Steane
  code; nothing is checked on 49 qubits.
-/
