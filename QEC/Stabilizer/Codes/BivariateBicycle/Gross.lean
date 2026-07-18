import QEC.Stabilizer.Codes.BivariateBicycle.Gross.Defs
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.CRTFrame
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.CoverTransfer
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.DeckHomotopy
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.Witness
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.Assembly
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.BaseDistance
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.DangerousSector
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.SafeSector
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.StabilizerCode
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.LightStab
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.LightStabClassify
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.SafeFloor
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.LayerInstance

/-!
# The gross `[[144,12,12]]` code — instance umbrella (proof spine)

Chain-level formalization of the gross bivariate-bicycle code and its
`[[72,12,6]]` base, related by a 2:1 covering. Import order = read order:

- `Defs`          — groups, polynomials, chain complexes, covering data
- `CRTFrame`      — the CRT layer frame (A4 §3): computable F₄, the group
                    algebra `F₄[Z₂²]`, layer/torus coordinates, and the engine
                    support-shape lemma
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
- `StabilizerCode` — the `[[144,12,12]]` packaging (trimmed generators,
                    decoder identities, independence, closure equality)
- `LightStab`     — light-stabilizer engine substrate
- `LightStabClassify` — **discharges `LightStabilizerClassification`**
                    (`lightStabilizerClassification_holds`) by the effective
                    CRT-engine classification, making `DangerousSectorGe12`
                    unconditional
- `SafeFloor/`    — everything discharging `MImBound` (the safe-sector floor):
                    engine + Tier-3 analytic track; see `SafeFloor.lean`
- `LayerInstance` — the gross ↔ bb72 cover packaged as `grossCoverData :
                    XDoubleCoverData`, and the unconditional `d(gross) = 12`
                    re-derived through the parametric doubling layer
                    (`gross_chain_distance_eq_12`, `gross_pauli_distance_eq_12`)
                    with every layer input discharged by the existing gross
                    theorems — no `native_decide` leaf re-run

Both CRT-engine inputs — `LightStabilizerClassification` (`LightStabClassify`)
and `MImBound` (`SafeFloor/MImAssembly`) — are discharged, so the distance of
the gross `[[144,12,12]]` code is **unconditional and axiom-clean** (the
standard three axioms + the `native_decide` compiler axiom; no `sorry`).
See `../README.md` for the discharge map and status board.
-/
