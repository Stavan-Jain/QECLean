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
import QEC.Stabilizer.Codes.BivariateBicycle.LightStabClassify
import QEC.Stabilizer.Codes.BivariateBicycle.MImClassify
import QEC.Stabilizer.Codes.BivariateBicycle.MImFloorData
import QEC.Stabilizer.Codes.BivariateBicycle.MImFloor
import QEC.Stabilizer.Codes.BivariateBicycle.MImMembership
import QEC.Stabilizer.Codes.BivariateBicycle.MImTransport
import QEC.Stabilizer.Codes.BivariateBicycle.MImFloorY0
import QEC.Stabilizer.Codes.BivariateBicycle.MImFloorY1
import QEC.Stabilizer.Codes.BivariateBicycle.MImFloorY2
import QEC.Stabilizer.Codes.BivariateBicycle.MImFloorY3
import QEC.Stabilizer.Codes.BivariateBicycle.MImFloorY4
import QEC.Stabilizer.Codes.BivariateBicycle.MImFloorY5
import QEC.Stabilizer.Codes.BivariateBicycle.MImFloorY6
import QEC.Stabilizer.Codes.BivariateBicycle.MImFloorY7
import QEC.Stabilizer.Codes.BivariateBicycle.MImFloorY8
import QEC.Stabilizer.Codes.BivariateBicycle.MImFloorY9
import QEC.Stabilizer.Codes.BivariateBicycle.MImFloorY10
import QEC.Stabilizer.Codes.BivariateBicycle.MImFloorY11
import QEC.Stabilizer.Codes.BivariateBicycle.MImFloorY12

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
                    `LightStabilizerClassification` hypothesis
- `SafeSector`    — the Smith-coset reduction (from the deck homotopy (R))
                    of the safe sector to the single `MImBound` hypothesis;
                    final assembly `gross_pauli_distance_eq_12_of_engine`
- `LightStabClassify` — **discharges `LightStabilizerClassification`**
                    (`lightStabilizerClassification_holds`) by the effective
                    CRT-engine classification, making `DangerousSectorGe12`
                    unconditional
- `MImClassify`   — the safe-sector confined-frame floor (A4 §§9–13) toward
                    discharging `MImBound`: the weight join (`chainWeight` as a
                    per-block per-layer sum), the coset parity, and the `ker ∂₂`
                    basis with M-VANISH (`off₀ = off₂ = 0`), the closed weight
                    form (`costFromComps`), and the coset `f`-dependence. WIP.
- `MImFloorData`  — machine-generated cost tables (`D3V`, `RCELL`) and Γⱼ coset-generator
                    / fiber data for the floor engine (orbit-independent; emitted by
                    `scripts/gen_floor_lean.py`)
- `MImFloor`      — the native-decidable confined-floor engine: the Nat-encoded per-cell
                    cost (`exCost`), the slab-min / offset-aware relaxed lower bounds
                    (`slabMin`, `relaxed`), their soundness keystones (`cellMin_le`,
                    `rcell_le`) and monotone lemmas (`slabMin_le_exCost`,
                    `relaxed_le_exCost`), underpinning the `floorOK` two-phase decision
                    (validated `true` for all five orbits). WIP toward `mimBound_holds`.
- `MImMembership` — the Γ-membership indices (`gammaIdx0`..`gammaIdx4`) and their correctness
                    (`mem0`..`mem4`, `native_decide`): each `rmul P̂ⱼ (Vⱼ f)` sits at the
                    computed index in Γⱼ, on both blocks (the B̂/Â engine-multiplier
                    convention, verified against `seamC`)

The full `StabilizerCode` packaging is complete and the A4 §6.3 classification
hypothesis is discharged in `LightStabClassify`, leaving `MImBound` (A4 Part II
(M-im)) as the single remaining CRT-engine hypothesis for `d = 12`; its discharge
is under construction in `MImClassify`.
-/
