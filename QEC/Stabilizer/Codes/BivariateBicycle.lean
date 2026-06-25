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
import QEC.Stabilizer.Codes.BivariateBicycle.MImFloorY4
import QEC.Stabilizer.Codes.BivariateBicycle.MImFloorY11
import QEC.Stabilizer.Codes.BivariateBicycle.MImFloorY12
import QEC.Stabilizer.Codes.BivariateBicycle.MImAssembly
import QEC.Stabilizer.Codes.BivariateBicycle.SlotFrame
import QEC.Stabilizer.Codes.BivariateBicycle.WtFloor24
import QEC.Stabilizer.Codes.BivariateBicycle.WtFloor24Bridge

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
- `MImClassify`   — the safe-sector confined-frame floor *reduction* (A4 §§9–13): the weight
                    join (`chainWeight` as a per-block per-layer sum), the `ker ∂₂` basis with
                    M-VANISH (`off₀ = off₂ = 0`), the exact per-slot weight (Fourier bijection),
                    and the closed coset weight form `chainWeight_coset_eq` (= `costFromComps` of
                    the seam offsets ⊕ engine-multiplied free datum)
- `MImFloorData`  — machine-generated cost tables (`D3V`, `RCELL`) and Γⱼ coset-generator
                    / fiber data for the floor engine (orbit-independent; emitted by
                    `scripts/gen_floor_lean.py`)
- `MImFloor`      — the native-decidable confined-floor engine: the Nat-encoded per-cell cost
                    (`exCost`), the slab-min / offset-aware relaxed lower bounds (`slabMin`,
                    `relaxed`), their soundness keystones (`cellMin_le`, `rcell_le`) and monotone
                    lemmas, plus the structural / flat-index soundness (`floorOK_sound`/`_flat`)
                    and the chain-weight bridge (`costFromComps_eq_exCost`)
- `MImMembership` — the Γ-membership indices (`gammaIdx0`..`gammaIdx4`) and their correctness
                    (`mem0`..`mem4`, `native_decide`: each `rmul P̂ⱼ (Vⱼ f)` sits at the computed
                    index in Γⱼ), plus the general per-orbit floor `floor_of_data`
- `MImTransport`  — the translation symmetry.  `seamC` is y-covariant at the chain level
                    (`seamC_shiftYk_combo`); in x it is covariant only up to an explicit
                    boundary defect (the §9.3 cut-shift).  Both are captured by the general
                    `floor_transfer` (§17), which lifts a class's floor to any `(j,k)`-translate;
                    `chainWeight` translation-invariance does the rest.
- `MImFloorY{0,1,4,11,12}` — the safe-sector floor proven for the 5 full-translation-orbit
                    representatives (per-orbit `native_decide` `floorOK = true` leaf +
                    `floor_of_data`)
- `MImAssembly`   — **discharges `MImBound`** (`mimBound_holds`): the 64-case 2-D-orbit dispatch
                    (`floor_kcombo`) reduces every `ker ∂₂` class to one of the 5 reps; then the
                    **unconditional** `grossStabilizerCode_hasCodeDistance_12_uncond` and the
                    bundled `grossStabilizerCodeWithDistance : StabilizerCodeWithDistance 144 12 12`

- `SlotFrame`     — **(Tier 3, A4 §10) analytic slot-frame infrastructure** that will replace
                    the `native_decide` confined-floor engine (`MImFloor`/`floorOK`).  The
                    integration bridge `floor_of_data_analytic` (mirrors `floor_of_data`'s
                    signature, via `chainWeight_coset_eq`), the slot algebra (kill vector
                    `kappa`, labelings `ellL`/`ellR`, `theta`), Lemma 19 (labeling facts),
                    the per-slot cost lower bounds `mFree1`/`mFree2` + soundness (Lemma 20,
                    by `omega` — axiom-clean), the link-free block bound
                    `costFromComps_ge_blockLB`, and the affine-pencil / hyperbolic-quadruple
                    facts (Lemmas 21, 24).  This is the §10 substrate; the per-orbit floor
                    walks (§§11–13) that consume it are still TODO, so the floor remains
                    discharged by `MImAssembly`'s engine for now.
- `WtFloor24`     — **(Tier 3, A4 §11) the weight-24 standard-form walk** (M1a).  The per-slot
                    cost `slotCost` (Lemma 20) + soundness `slotCost_le`, the standard form
                    `Sab` (Def 26), and **Proposition 29** `Sab_ge_6` (`S(a,b) ≥ 6` ∀ 16 pairs,
                    so every wt-24 spine cell has linked block cost `≥ 12`).  Axiom-clean
                    (kernel `decide`).  The bridge to the actual wt-24 floor (M1b) is TODO.
- `WtFloor24Bridge` — **(Tier 3, A4 §§10–11) the weight-24 floor bridge substrate** (M1b).
                    The verified plumbing connecting the closed coset weight `costFromComps`
                    (the `floor_of_data_analytic` hypothesis) to the `slotCost` machinery:
                    radical-multiplier image membership (`rmul_{Bhat2,Ahat1,Ahat4}_mem`,
                    `inIdeal_to_exists`), the slot-sum expansion (`sum_zmod2sq`), the
                    `Fin 2 ↪ Fin 4` component-0 bridge (`slotCost(L)_le'`), component 0's
                    `F₂`-valuedness (`V_psi0_lt2`, `comp0_lt2_{L,R}`), the block split
                    (`costFromComps_ge_blockSlotCost`), the cost-preserving moves (Lemma 25:
                    `slotCost(L)_frob`, `slotCost_scale`), and the standard-form right-block
                    bound (`RBlock_std_ge6`).  Establishes (by `decide`) that the
                    decoupled per-block bound is insufficient (raw `Y4` offsets are
                    non-standard) and the standard-form reduction (Lemma 27) is required to
                    discharge the two wt-24 leaves — the remaining M1b work.

Both CRT-engine inputs — `LightStabilizerClassification` (`LightStabClassify`) and `MImBound`
(`MImAssembly`) — are now discharged, so the distance of the gross `[[144,12,12]]` code is
**unconditional and axiom-clean** (the standard three axioms + the `native_decide` compiler
axiom; no `sorry`).
-/
