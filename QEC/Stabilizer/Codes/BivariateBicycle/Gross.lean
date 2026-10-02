import QEC.Stabilizer.Codes.BivariateBicycle.Gross.Defs
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.CRTFrame
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.CoverTransfer
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.DeckHomotopy
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.Witness
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.Assembly
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.BaseDistance
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.DangerousSector
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.SafeSector
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.StabilizerCodeData
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.StabilizerCode
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.LightStab
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.LightStabClassify
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.SafeFloor
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.LayerInstance
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.Distance

/-!
# The gross `[[144,12,12]]` code — instance umbrella (proof spine)

Chain-level formalization of the gross bivariate-bicycle code and its
`[[72,12,6]]` base, related by a 2:1 covering. Import order = read order:

- `Defs` — groups, polynomials, chain complexes, covering data
- `CRTFrame` — the CRT layer frame (A4 §3): computable F₄, the group algebra
  `F₄[Z₂²]`, layer/torus coordinates, and the engine support-shape lemma
- `CoverTransfer` — `grossCoverData`, with transfer maps, exactness, and
  weight identities from `BBCover`
- `DeckHomotopy` — the Gross polynomial certificate for the generic Bézout
  homotopy: `v + σv` bounds for every cycle `v`
- `Witness` — the explicit weight-12 nontrivial cycle `τ(u*)`
- `Assembly` — the conditional `d(gross) = 12`: sector dichotomy with the three
  analytic inputs (`BaseDistanceGe6`, `DangerousSectorGe12`, `SafeSectorGe12`)
  as aliases of the generic inputs; all assemblies use the logical-floor
  doubling theorems
- `BaseDistance` — `BaseDistanceGe6` discharged through `SmallCycleData`
  with kernel-checked finite certificates ⟹ **unconditional d(gross) ≥ 6**
- `DangerousSector` — generic slice and logical-floor rung applications,
  Gross shape certificates, and (M) modulo the
  `LightStabilizerClassification` hypothesis
- `SafeSector` — the Smith-coset reduction (from the deck homotopy (R)) of the
  safe sector to the single `MImBound` hypothesis; final assembly
  `gross_pauli_distance_eq_12_of_engine`
- `StabilizerCode` — the `[[144,12,12]]` packaging (trimmed generators, decoder
  identities, independence, closure equality)
- `LightStab` — light-stabilizer engine substrate
- `LightStabClassify` — **discharges `LightStabilizerClassification`**
  (`lightStabilizerClassification_holds`) by the effective CRT-engine
  classification, making `DangerousSectorGe12` unconditional
- `SafeFloor/` — everything discharging `MImBound` (the safe-sector floor), all
  of it Tier-3 analytic; see `SafeFloor.lean`
- `LayerInstance` — the unconditional chain and Pauli distances from the
  generic logical-floor doubling assembly, with both sector inputs discharged
- `Distance` — the capstones (`grossStabilizerCode_hasCodeDistance_12_uncond`,
  `grossStabilizerCodeWithDistance`), packaging that same generic result

Both CRT-engine inputs — `LightStabilizerClassification` (`LightStabClassify`)
and `MImBound` (`SafeFloor/MImAssembly`) — are discharged, so the distance of
the gross `[[144,12,12]]` code is **unconditional and kernel-only**: the
capstones depend on exactly `propext`, `Classical.choice` and `Quot.sound` — no
`native_decide` (hence no compiler-trust axiom) and no `sorry` anywhere in the
cone. See `../README.md` for the discharge map and status board.
-/
