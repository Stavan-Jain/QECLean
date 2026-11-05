import QEC.Stabilizer.Codes.Small.FourQubitPacking
import QEC.Stabilizer.Codes.Small.Shor9
import QEC.Stabilizer.Codes.Small.Shor9Logicals
import QEC.Stabilizer.Codes.Small.Steane7
import QEC.Stabilizer.Codes.Small.Steane7Logicals
import QEC.Stabilizer.Codes.Small.Steane7TransversalGates
import QEC.Stabilizer.Codes.Small.FourQubit_4_2_2
import QEC.Stabilizer.Codes.Small.FourQubit_4_2_2Logicals
import QEC.Stabilizer.Codes.Small.QuantumHamming
import QEC.Stabilizer.Codes.Small.QuantumHammingLogicals
import QEC.Stabilizer.Codes.Small.FiveQubit_5_1_3
import QEC.Stabilizer.Codes.Small.FiveQubit_5_1_3Logicals
import QEC.Stabilizer.Codes.Small.CSS_4_1_2
import QEC.Stabilizer.Codes.Small.CSS_4_1_2Logicals
import QEC.Stabilizer.Codes.Small.SixQubit_6_2_2
import QEC.Stabilizer.Codes.Small.SixQubit_6_2_2Logicals

/-!
# Small concrete codes

Single-instance stabilizer codes: Shor's [[9,1,3]], Steane [[7,1,3]] (with
transversal gates), the [[4,2,2]] code, quantum Hamming, the [[5,1,3]] perfect
code (the first non-CSS code in the repo), the [[4,1,2]] LNCY CSS detection
code, and Knill's C_6 [[6,2,2]] CSS detection code.

Every code has the same two-file layout:
- `<Code>.lean` — the generators, the bundled `stabilizerCode`, and its
  distance proof, ending in `stabilizerCodeWithDistance`. Self-contained: the
  distance witness carries its own nontriviality proof, so nothing here depends
  on a choice of logical basis.
- `<Code>Logicals.lean` — the chosen logical basis, its (anti)commutation and
  centralizer membership, ending in `stabilizerCodeWithLogicals`.

Quantum Hamming, a parametric family, has no full logical basis yet, so its
logicals file stops short of `stabilizerCodeWithLogicals`. Code-specific
extras, such as `Steane7TransversalGates.lean`, build on the logicals file.

`FourQubitPacking.lean` is an additional homological example of the four-qubit
code. It demonstrates weighted packing and complete logical coverage without
changing the existing generator-presentation code or its chosen logical basis.
-/
