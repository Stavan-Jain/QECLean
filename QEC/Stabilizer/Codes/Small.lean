import QEC.Stabilizer.Codes.Small.CSS_4_1_2
import QEC.Stabilizer.Codes.Small.CSS_4_1_2Logicals
import QEC.Stabilizer.Codes.Small.FiveQubit_5_1_3
import QEC.Stabilizer.Codes.Small.FiveQubit_5_1_3Logicals
import QEC.Stabilizer.Codes.Small.FourQubit_4_2_2
import QEC.Stabilizer.Codes.Small.FourQubit_4_2_2Logicals
import QEC.Stabilizer.Codes.Small.QuantumHamming
import QEC.Stabilizer.Codes.Small.QuantumHammingLogicals
import QEC.Stabilizer.Codes.Small.Shor9
import QEC.Stabilizer.Codes.Small.Shor9Logicals
import QEC.Stabilizer.Codes.Small.SixQubit_6_2_2
import QEC.Stabilizer.Codes.Small.SixQubit_6_2_2Logicals
import QEC.Stabilizer.Codes.Small.Steane7
import QEC.Stabilizer.Codes.Small.Steane7Logicals
import QEC.Stabilizer.Codes.Small.Steane7TransversalGates

/-!
# Small concrete codes

Stabilizer codes on a fixed, small number of qubits, and the quantum Hamming
family. Every code has the same two-file layout, described in
`Codes/_TEMPLATE.lean`: `<Code>.lean` runs from the generators to the code with
its distance, `stabilizerCodeWithDistance`, and `<Code>Logicals.lean` adds a
logical basis, ending in `stabilizerCodeWithLogicals`.

- `CSS_4_1_2`, `CSS_4_1_2Logicals`: the LNCY code `[[4, 1, 2]]`, a CSS
  detection code with one logical qubit.
- `FourQubit_4_2_2`, `FourQubit_4_2_2Logicals`: the four-qubit detection code
  `[[4, 2, 2]]`, with two logical qubits.
- `SixQubit_6_2_2`, `SixQubit_6_2_2Logicals`: the six-qubit code `C₆`,
  `[[6, 2, 2]]`, with two logical qubits.
- `FiveQubit_5_1_3`, `FiveQubit_5_1_3Logicals`: the five-qubit code
  `[[5, 1, 3]]`, which is not CSS.
- `Steane7`, `Steane7Logicals`: the Steane code `[[7, 1, 3]]`.
- `Steane7TransversalGates`: transversal `H` and `S` are logical gates of the
  Steane code, acting as the logical Hadamard and phase gates.
- `Shor9`, `Shor9Logicals`: Shor's code `[[9, 1, 3]]`, a degenerate code.
- `QuantumHamming`, `QuantumHammingLogicals`: the quantum Hamming codes
  `[[2^r − 1, 2^r − 1 − 2r, 3]]` for `r ≥ 3`, with the transversal logical pair
  `X⊗ⁿ`, `Z⊗ⁿ`.
-/
