import QEC.Stabilizer.Codes.BivariateBicycle.Defs
import QEC.Stabilizer.Codes.BivariateBicycle.CRTFrame
import QEC.Stabilizer.Codes.BivariateBicycle.CoverTransfer
import QEC.Stabilizer.Codes.BivariateBicycle.DeckHomotopy
import QEC.Stabilizer.Codes.BivariateBicycle.Witness
import QEC.Stabilizer.Codes.BivariateBicycle.Assembly
import QEC.Stabilizer.Codes.BivariateBicycle.BaseDistance
import QEC.Stabilizer.Codes.BivariateBicycle.DangerousSector
import QEC.Stabilizer.Codes.BivariateBicycle.SafeSector
import QEC.Stabilizer.Codes.BivariateBicycle.StabilizerCode
import QEC.Stabilizer.Codes.BivariateBicycle.LightStab

/-!
# Bivariate bicycle codes

Chain-level formalization of the gross `[[144, 12, 12]]` bivariate bicycle
code and its `[[72, 12, 6]]` base, related by a 2:1 covering:

- `Defs`          — groups, polynomials, chain complexes, covering data
- `CRTFrame`      — the CRT layer frame (A4 §3): computable F₄, the group
                    algebra `F₄[Z₂²]`, layer/torus coordinates, and the engine
                    support-shape lemma (M1 + M3 foundation for discharging the
                    two CRT-engine hypotheses; M2 multiplicativity is next)
- `CoverTransfer` — pushforward/pullback chain maps, exactness, weight identity
- `DeckHomotopy`  — the deck homotopy (R): `v + σv` bounds for every cycle `v`
- `Witness`       — the explicit weight-12 nontrivial cycle `τ(u*)`
- `Assembly`      — the conditional `d(gross) = 12`: sector dichotomy with
                    the three analytic inputs (`BaseDistanceGe6`,
                    `DangerousSectorGe12`, `SafeSectorGe12`) as named
                    hypotheses, the `b = 0` rung discharged, and the
                    Pauli-level corollaries
- `BaseDistance`  — `BaseDistanceGe6` discharged (small-cycle theorem,
                    verified-finite leaf) ⟹ **unconditional d(gross) ≥ 6**
- `DangerousSector` — the slice identity, the m-rungs, and (M) modulo the
                    single `LightStabilizerClassification` hypothesis
- `SafeSector`    — the Smith-coset reduction (from the deck homotopy (R))
                    of the safe sector to the single `MImBound` hypothesis;
                    final assembly `gross_pauli_distance_eq_12_of_engine`

The full `StabilizerCode` packaging and the discharge of the two remaining
CRT-engine hypotheses (A4 §6.3 classification; A4 Part II (M-im)) are later
phases.
-/
