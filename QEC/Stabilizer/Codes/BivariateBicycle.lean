import QEC.Stabilizer.Codes.BivariateBicycle.Defs
import QEC.Stabilizer.Codes.BivariateBicycle.CoverTransfer
import QEC.Stabilizer.Codes.BivariateBicycle.DeckHomotopy
import QEC.Stabilizer.Codes.BivariateBicycle.Witness
import QEC.Stabilizer.Codes.BivariateBicycle.Assembly

/-!
# Bivariate bicycle codes

Chain-level formalization of the gross `[[144, 12, 12]]` bivariate bicycle
code and its `[[72, 12, 6]]` base, related by a 2:1 covering:

- `Defs`          — groups, polynomials, chain complexes, covering data
- `CoverTransfer` — pushforward/pullback chain maps, exactness, weight identity
- `DeckHomotopy`  — the deck homotopy (R): `v + σv` bounds for every cycle `v`
- `Witness`       — the explicit weight-12 nontrivial cycle `τ(u*)`
- `Assembly`      — the conditional `d(gross) = 12`: sector dichotomy with
                    the three analytic inputs (`BaseDistanceGe6`,
                    `DangerousSectorGe12`, `SafeSectorGe12`) as named
                    hypotheses, the `b = 0` rung discharged, and the
                    Pauli-level corollaries

The full `StabilizerCode` packaging and the discharge of the three sector
hypotheses (A4 Theorems A/C/D) are later phases.
-/
