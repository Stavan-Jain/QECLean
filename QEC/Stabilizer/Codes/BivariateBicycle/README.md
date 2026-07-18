# BivariateBicycle — orientation (read me before editing)

Every bivariate-bicycle **instance** lives in its own subdirectory with a
sibling umbrella `.lean`; the shared theory lives in
`Framework/Homological/BB*` (`BBChainComplex`, `BBCover`, `BBDoubling`,
`BBDeckTower`, `BBBocksteinRank`, `BBEpsFree*`, `BBSmallCycle`,
`BBDeficitWall`). This README is the task router and status board; the
per-module one-liner maps live in the umbrella docstrings (`Gross.lean`,
`Gross/SafeFloor.lean`, `Z3Z6.lean`, …).

## Instances

| Dir | Code | Distance status |
|---|---|---|
| `Gross/` | gross `[[144,12,12]]` (base `[[72,12,6]]`) | **d = 12 unconditional** (axiom-clean + `native_decide`; also re-derived through the parametric layer in `Gross/LayerInstance.lean`) |
| `Z3Z6/` | pair72 `[[36,4,4]] → [[72,4,8]]` | d = 8 unconditional (the canonical complete instance — copy this shape) |
| `Z5Z15F2A6/` | `[[150,8,8]] → [[300,8,16]]` two-tier | in progress (A17 line; minimal starting skeleton to copy) |
| `BaseFloors/` | class-member base floors (BB90, BB108, Z6Z14) | d ≥ 6 kernel-checked via `BBSmallCycle` (A15/A16 class theorem) |

## Task router

- **Understand the gross d = 12 proof**: read `Gross.lean`'s docstring, then
  the spine in umbrella order (Defs → CRTFrame/CoverTransfer → DeckHomotopy →
  Witness → Assembly → BaseDistance → DangerousSector → SafeSector →
  LightStab → LightStabClassify → StabilizerCode). Paper version:
  `qec-lab:docs/gross-distance-proof.md`.
- **Tier-3 analytic work** (retiring `native_decide` leaves; A7 Props 30–31):
  `Gross/SafeFloor/WtFloor1618.lean` + `WtFloor24Bridge.lean`.
- **Regenerate a table / change generated data**: see the generated-files
  table below and `qec-lab:experiments/bb_lab/GENERATORS.md`. Never hand-edit a
  Class-G file.
- **Add a new instance**: follow "Adding an instance" below.
- **Change the doubling layer itself**: `Framework/Homological/BBDoubling.lean`
  (not this directory); its per-instance inputs are documented there.

## Hypothesis-discharge map (gross)

| Named hypothesis | Discharged by | Grade |
|---|---|---|
| `BaseDistanceGe6` | `Gross/BaseDistance.lean` (small-cycle theorem) | kernel `decide` + analytic |
| `LightStabilizerClassification` | `Gross/LightStabClassify.lean` (`lightStabilizerClassification_holds`) | engine (`native_decide`) |
| `DangerousSectorGe12` | `Gross/DangerousSector.lean` ((M), m-rungs) | analytic, engine-fed |
| `SafeSectorGe12` → `MImBound` | `Gross/SafeSector.lean` (Smith-coset reduction) | analytic |
| `MImBound` | `Gross/SafeFloor/MImAssembly.lean` (`mimBound_holds`, 64-case dispatch → 5 orbit reps) | mixed (see per-orbit rows) |
| — orbit Y0/Y1/Y4 (wt 16/18) | `SafeFloor/MImFloorY{0,1,4}.lean` (`floor_of_data` engine leaf) | engine (`native_decide`) — flips analytic when A7 Props 30–31 close |
| — orbit Y11/Y12 (wt 24) | `SafeFloor/MImFloorY{11,12}.lean` via `WtFloor24Bridge.costFromComps_ge_12_of_blocks` | **analytic** (kernel `decide`) |
| capstones | `Gross/Distance.lean` (`grossStabilizerCode_hasCodeDistance_12_uncond`, `grossStabilizerCodeWithDistance`) + `Gross/LayerInstance.lean` (`gross_chain/pauli_distance_eq_12` through the layer) | — |

Z3Z6 mirror: `StrongBaseFloor 4` → `Z3Z6/BaseDistance.lean`; `DeckTrivialOnH1`
→ `Z3Z6/DeckHomotopy.lean`; `DangerousFloorNZ 8` → `Z3Z6/Dangerous.lean`;
`SeamCosetFloor 8` → `Z3Z6/SafeFloor.lean` (sweep leaves); capstone
`Z3Z6/Distance.lean`.

## Engine vs analytic (native_decide counts, 2026-07-18)

`native_decide` total in this directory: ~303. Top carriers: gross
`StabilizerCode` 35 (§5 decoder identities — data file split out as
`StabilizerCodeData`), `LightStab` 30, `CRTFrame` 20, `MImFloor` 16,
`MImFloorY0/1/4` 16 each, `Z3Z6/StabilizerCode` 16, `LightStabClassify` 15.
The Tier-3 track (`SlotFrame` → `WtFloor24` → `WtFloor24Bridge` →
`WtFloor1618`) replaces engine leaves with analytic proofs; Y11/Y12 are
already flipped. Status changes belong HERE, not in module names.

## Generated files (Class G: fully generated — NEVER hand-edit)

| File | Generator (`qec-lab:experiments/bb_lab/`) | Data |
|---|---|---|
| `Gross/StabilizerCodeData.lean` | `phase5/gen_file.py` (`--force` guard; emits data only) | `phase5/data.json` |
| `Gross/SafeFloor/MImFloorData.lean` | `scripts/gen_floor_lean.py` | in-script |
| `Gross/SafeFloor/MImFloorY{0,1,4,11,12}.lean` | `scripts/gen_yrep_module.py <i>` | in-script |
| `Z3Z6/StabilizerCodeData.lean` | `scripts/gen_pair72_packaging_data.py` (retarget to data-only queued — do not run without reading GENERATORS.md) | validation-gated |
| `BaseFloors/*.lean` | `scripts/gen_base_floor_lean.py` | per-instance |

Class F (generated fragments between `-- BEGIN/END GENERATED` markers,
hand-curated shell): `Gross/SafeFloor/MImAssembly.lean`
(`scripts/gen_assembly_2d.py`). Everything else is Class H (hand-maintained;
may embed machine-*validated* data). Rule: **a hand-edit to a Class-G file is
a bug — change the generator and regenerate, in the same PR.** Operational
details (env, clobber guards, stale generators): `qec-lab:experiments/bb_lab/GENERATORS.md`.

## Edit rules

1. New module ⟹ `import` line in the NEAREST umbrella (`Gross.lean`,
   `Gross/SafeFloor.lean`, `<Instance>.lean`) — then run
   `bash scripts/check-umbrellas.sh` (orphan modules silently don't build).
2. Class-G files: regenerate, never edit (banner at the top of each).
3. `native_decide` is allowed (repo policy); no `set_option linter.* false`.
4. Heavy files carry `maxRecDepth`/`maxHeartbeats` headers — don't copy them
   into new files without need.
5. One lake process at a time (see CLAUDE.md).

## Adding an instance

Copy the shape of `Z3Z6/` (complete) or `Z5Z15F2A6/` (minimal skeleton):

1. `mkdir <Name>/` + sibling `<Name>.lean` umbrella. Name = base group +
   disambiguating tag (`Z3Z6`, `Z5Z15F2A6` precedent).
2. Minimum files, in dependency order: `Defs.lean` (complexes +
   `XDoubleCoverData` bundle against `Framework/Homological/BBCover.lean`) →
   `DeckHomotopy.lean` (Bezout witness via `deckTrivial_of_bezout`) →
   `Witness.lean` → `BaseDistance.lean` (`StrongBaseFloor d`, or a
   `BaseFloors/` bundle via `BBSmallCycle`) → `Dangerous.lean` →
   `SafeFloor.lean` (+ `MaskDefs`/`SeamTables`/`Sweep*` leaves, one file per
   sweep) → `Distance.lean` (capstone) → `StabilizerCodeData.lean` +
   `StabilizerCode.lean` (via a generator clone with validation gate +
   `--force` guard).
3. Discharge the five `BBDoubling` inputs by name: `StrongBaseFloor`,
   `DeckTrivialOnH1`, `DangerousFloorNZ`, `SeamCosetFloor`, tight witness.
4. Wire umbrellas (rule 1); add the instance row to the table above and, if
   generators are involved, rows in the generated-files table + GENERATORS.md.

## Staleness contract

Any PR that adds/moves/renames a module here, flips a leaf engine→analytic,
changes a generator, or adds an instance MUST update this README (the tables
are keyed by stable names — that is the anti-staleness design). A PR touching
`BivariateBicycle/**` structure without touching this file is suspect.
