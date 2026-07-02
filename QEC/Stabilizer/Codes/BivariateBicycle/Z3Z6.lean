import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.Defs
import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.BaseDistance
import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.DeckHomotopy
import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.Witness
import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.MaskDefs
import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.SeamTables
import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.SweepKer
import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.SweepClassify
import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.SweepSafe10
import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.SweepSafe01
import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.SweepSafe11
import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.LightStab
import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.Dangerous
import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.SafeFloor
import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.Distance

/-!
# The [[36,4,4]] → [[72,4,8]] doubling pair over `Z₃×Z₆ → Z₆×Z₆`

The second full instance of the free-ℤ₂ doubling template — the pair of
`docs/gross-distance-extensibility.md` §5, previously verified only by
SAT, now proven through the parametric layer
(`Framework/Homological/{BBCover,BBDoubling}.lean`):

- `Defs`         — groups, polynomials, complexes, the `coverData` bundle
- `BaseDistance` — `StrongBaseFloor 4` (weight-1/2/3 kernel sweeps) and the
                   unconditional Theorem-B cover floor `d(cover) ≥ 4`
- `DeckHomotopy` — the homotopy (R) via the single identity `p⋆B = 1+x³`
- `Witness`      — the weight-4 `u*` and its weight-8 nontrivial lift `τ(u*)`
- `MaskDefs`     — the `ker ∂₂` basis and the `Fin (2¹⁸)` mask encoding the
                   sweep leaves quantify over
- `SeamTables`   — the three class seams `seamC (kcombo c₀ c₁)` tabulated as
                   literal chains (certified by kernel identities), so the
                   safe-floor sweeps don't re-derive a 72-entry constant
                   `2¹⁸` times
- `Sweep{Ker,Classify,Safe10,Safe01,Safe11}` — the five `2¹⁸` kernel-sweep
                   leaves, one file each so `lake` builds them in parallel
                   (the `MImFloorY*` pattern; minutes of native compute per leaf)
- `LightStab`    — the ∀-chain forms: direct `ker ∂₂` spanning and the
                   light-boundary classification with seam-good preimages
- `Dangerous`    — `DangerousFloorNZ 8` via the generic single-shape rung
- `SafeFloor`    — `SeamCosetFloor 8`: the three per-class floors assembled
                   (no CRT engine at this scale)
- `Distance`     — `d = 8` at the chain and Pauli levels
                   (`pair72_chain_distance_eq_8`, `pair72_pauli_distance_eq_8`)
-/
