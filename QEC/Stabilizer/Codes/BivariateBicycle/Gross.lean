import QEC.Stabilizer.Codes.BivariateBicycle.Gross.Defs
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.CoverTransfer
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.DeckHomotopy
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.Witness
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.Assembly
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.BaseDistance
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.DangerousSector
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.SafeSector
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.StabilizerCodeData
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.StabilizerCode
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.SeamBZData
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.SeamBZWalk
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.SeamBZ
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.LayerInstance
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.Distance

/-!
# The gross `[[144,12,12]]` code — instance umbrella (proof spine)

Chain-level formalization of the gross bivariate-bicycle code and its
`[[72,12,6]]` base, related by a 2:1 covering. Import order = read order:

- `Defs` — groups, polynomials, chain complexes, covering data
- `CoverTransfer` — `grossCoverData`, with transfer maps, exactness, and
  weight identities from `BBCover`
- `DeckHomotopy` — the Gross polynomial certificate for the generic Bézout
  homotopy: `v + σv` bounds for every cycle `v`
- `Witness` — the explicit weight-12 nontrivial cycle `τ(u*)`
- `Assembly` — the conditional `d(gross) = 12`: sector dichotomy with the three
  inputs (`BaseDistanceGe6`, `DangerousSectorGe12`, `SafeSectorGe12`) as aliases
  of the generic inputs; all assemblies use the logical-floor doubling theorems
- `BaseDistance` — `BaseDistanceGe6` discharged through `SmallCycleData`
  with kernel-checked finite certificates ⟹ **unconditional d(gross) ≥ 6**
- `DangerousSector` — generic slice and logical-floor rung applications,
  Gross shape certificates, and (M) modulo `LightStabilizerClassification`
- `SafeSector` — the Smith-coset reduction (from the deck homotopy (R)) of the
  safe sector to `MImBound`, and the sparse form of `seamC`
- `StabilizerCodeData` + `StabilizerCode` — the `[[144,12]]` packaging (trimmed
  generators, decoder identities, independence, closure equality)
- `SeamBZData` + `SeamBZWalk` + `SeamBZ` — **one Brouwer–Zimmermann
  certificate** for the generic `SeamBZCertificate`
  (`Framework/Homological/BBSeamBZ.lean`) that discharges both `MImBound`
  (`GrossBZ.mimBound_bz`) and `LightStabilizerClassification`
  (`GrossBZ.lightStabilizerClassification_bz`)
- `LayerInstance` — the unconditional chain and Pauli distances, each one
  application of the packaged Doubling theorem
  (`pauli_distance_eq_double_of_admissible`), with the light-boundary census
  as its admissibility input
- `Distance` — the capstones (`grossStabilizerCode_hasCodeDistance_12_uncond`,
  `grossStabilizerCodeWithDistance`), packaging that same generic result

The distance of the gross `[[144,12,12]]` code is **unconditional and
kernel-only**: the capstones depend on exactly `propext`, `Classical.choice`
and `Quot.sound` — no `native_decide` and no `sorry` anywhere in the cone. See
`../README.md` for the discharge map and status board.
-/
