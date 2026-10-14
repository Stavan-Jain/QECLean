import QEC.Stabilizer.Codes.Repetition.Three
import QEC.Stabilizer.Codes.Repetition.ThreeLogicals
import QEC.Stabilizer.Codes.Repetition.N
import QEC.Stabilizer.Codes.Repetition.NLogicals

/-!
# Repetition codes

Classical repetition codes, embedded as degenerate distance-1 quantum stabilizer
codes: the 3-qubit instance (`Three`) and the parametric `[[n+2, 1, 1]]` family
(`N`).

Each follows the same two-file layout as `Codes/Small/`: `Three.lean` / `N.lean`
run from the generators to `stabilizerCodeWithDistance`, and
`ThreeLogicals.lean` / `NLogicals.lean` add the logical basis and
`stabilizerCodeWithLogicals`.
-/
