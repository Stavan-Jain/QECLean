# BivariateBicycle — orientation (read me before editing)

Every bivariate-bicycle **instance** lives in its own subdirectory with a
sibling umbrella `.lean`; the shared theory lives in
`Framework/Homological/BB*` (`BBChainComplex`, `BBCover`, `BBDoubling`,
`BBDeckTower`, `BBBocksteinRank`, `BBEpsFree*`, `BBSmallCycle`,
`BBDeficitWall`). This README is the task router and status board; the
per-module one-liner maps live in the umbrella docstrings (`Gross.lean`,
`Gross/SafeFloor.lean`, `Z5Z15F2A6.lean`, …).

## Instances

| Dir | Code | Distance status |
|---|---|---|
| `Gross/` | gross `[[144,12,12]]` (base `[[72,12,6]]`) | **d = 12 unconditional, kernel-only** — axioms are exactly `propext`, `Classical.choice`, `Quot.sound`; no `native_decide`, no `sorry` (also re-derived through the parametric layer in `Gross/LayerInstance.lean`) |
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
| `LightStabilizerClassification` | `Gross/LightStabClassify.lean` (`lightStabilizerClassification_holds`) | kernel `decide` |
| `DangerousSectorGe12` | `Gross/DangerousSector.lean` ((M), m-rungs) | analytic + kernel `decide` |
| `SafeSectorGe12` → `MImBound` | `Gross/SafeSector.lean` (Smith-coset reduction) | analytic |
| `MImBound` | `Gross/SafeFloor/MImAssembly.lean` (`mimBound_holds`, 64-case dispatch → 5 orbit reps) | analytic (see per-orbit rows) |
| — orbit Y0/Y1/Y4 (wt 16/18) | `SafeFloor/MImFloorY{0,1,4}.lean` via `LightFloor.floor_of_killOK` (the coupled spine certificate: Prop 30 `min_L + min_R ≥ 10` on all 1024 cells + Prop 31 ρ-link kill of the 10-tight cells) | **analytic** (kernel `decide`) |
| — orbit Y11/Y12 (wt 24) | `SafeFloor/MImFloorY{11,12}.lean` via `WtFloor24Bridge.costFromComps_ge_12_of_blocks` | **analytic** (kernel `decide`) |
| capstones | `Gross/Distance.lean` (`grossStabilizerCode_hasCodeDistance_12_uncond`, `grossStabilizerCodeWithDistance`) + `Gross/LayerInstance.lean` (`gross_chain/pauli_distance_eq_12` through the layer) | — |

The Z3Z6 (pair72, `[[36,4,4]] → [[72,4,8]]`) and Z5Z15F2A6
(`[[150,8,8]] → [[300,8,16]]`) instances, which used to mirror this map, are
**parked on branch `claude/z3z6-parked`** pending de-nativization — see
"Parked instances" below.

## Engine vs analytic (2026-08-20)

The gross `d = 12` cone contains **zero `native_decide`**: every leaf is a kernel
`decide` (mostly `decide +kernel`) or an analytic proof, so the capstones carry
only mathlib's three axioms. This is not an achievement local to `Gross/` — it is
the repo-wide bar: everything on `main` must print exactly
`[propext, Classical.choice, Quot.sound]`. See CLAUDE.md § "Axiom policy", and
park rather than merge anything that cannot meet it. The techniques, in the order they matter: packed-`Nat`
tables instead of `Array`/`List` lookups (an `Array.getD` is an O(n) list walk in
the kernel); quantifier bridges (`mkRing`, `mkTorus`, `chainOfMask`) that let the
kernel enumerate concrete lambdas rather than whnf a pi-`Fintype`; sparse rewrites
of `conv`/`∂₂`/`seamC` in place of `Finset.sum`s over the group; and Gaussian-style
certificates (the `ker ∂₂` peeling in `MImClassify.kerBasis_spans`) where a sweep
would otherwise be needed.

The Tier-3 track is complete: `SlotFrame` → `WtFloor24` → `WtFloor24Bridge`
closes the weight-24 orbits, and `WtFloor1618` → `LightFloor` closes the coupled
light orbits. The old confined-floor engine (`MImFloor`, `MImFloorData`,
`MImMembership` and their `2³⁰` `floorOK` walk) has been **retired** — those
modules are deleted, not merely unused. Status changes belong HERE, not in
module names.

`Gross/` is now the only BB instance in this tree, and the whole tree is
`native_decide`-free: the other instances (`Z5Z15F2A6/`, `BaseFloors/`) were
the last `native_decide` holders here and have been parked — see below.

## Parked instances

`main` is being driven to a `native_decide`-free state, so every instance that
still carried one has been removed from this tree and lives on branch
**`claude/z3z6-parked`**:

| Parked | Result given up | `native_decide` |
|---|---|---|
| `Z3Z6/` (pair72, `[[36,4,4]] → [[72,4,8]]`, d = 8 unconditional) | `pair72_*_distance_eq_8` | 42, five of them `2^18` sweeps that dominated a whole-repo build |
| `Z5Z15F2A6/` (`[[150,8,8]] → [[300,8,16]]`, two-tier) | `cover300_chain/pauli_distance_eq_16` | 9 (`Defs` coverData ×4, `Witness` ×4, `DeckHomotopy` Bezout ×1) |
| `BaseFloors/` (BB90, BB108, Z6Z14) | three certified `BBSmallCycle` class members | 12 (`epsA/epsB/check_two/check_four` ×3 files) |

`Z3Z6/PARKED.md` on that branch records the Z3Z6 rationale in detail. All three
are clean leaves — nothing outside each directory imported its declarations
(`Z5Z15F2A6/Distance.lean` is in-instance and went with it) — so restoring one
means re-adding the directory, its sibling umbrella, the import line in
`BivariateBicycle.lean`, and the rows removed from this README.

The abstract machinery they exercised stays in this tree:
`Framework/Homological/BBSmallCycle.lean` (the A15/A16 class small-cycle
theorem) and `BBDoubling`/`BBCover` are untouched — they simply have no
concrete instance here besides `Gross/`.

## Generated files (Class G: fully generated — NEVER hand-edit)

| File | Generator (`qec-lab:experiments/bb_lab/`) | Data |
|---|---|---|
| `Gross/StabilizerCodeData.lean` | `phase5/gen_file.py` (`--force` guard; emits data only) | `phase5/data.json` |
| `Gross/SafeFloor/MImFloorY{0,1,4}.lean` | **hand-maintained since the kernel-only conversion** (analytic Tier-3 form; formerly `gen_yrep_module.py`, which must be taught to refuse args 0/1/4) | — |
| `Gross/SafeFloor/MImFloorY{11,12}.lean` | **hand-maintained since PR #58** (analytic Tier-3 form; formerly `gen_yrep_module.py`, which now refuses args 11/12) | — |

**qec-lab follow-up owed**: `gen_floor_lean.py` now has no target in this repo
(`MImFloorData.lean` is deleted) and `gen_yrep_module.py` must refuse args 0/1/4
as it already refuses 11/12; both changes belong in a companion qec-lab PR.
| `BaseFloors/*.lean` | `scripts/gen_base_floor_lean.py` | per-instance |

Class F (generated fragments between `-- BEGIN/END GENERATED` markers,
hand-curated shell): `Gross/SafeFloor/MImAssembly.lean`
(`scripts/gen_assembly_2d.py`). Everything else is Class H (hand-maintained;
may embed machine-*validated* data). Rule: **a hand-edit to a Class-G file is
a bug — change the generator (in the qec-lab companion repo) and regenerate,
landing both repos' changes together.** Generators run from a sibling qec-lab
checkout and write here via `QECLEAN_ROOT` (default `../QECLean`). Operational
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

Copy the shape of `Gross/` (complete, kernel-only) — the only instance in this
tree; the parked `Z3Z6/` and `Z5Z15F2A6/` (branch `claude/z3z6-parked`) are
further worked examples:

1. `mkdir <Name>/` + sibling `<Name>.lean` umbrella. Name = base group +
   disambiguating tag (`Z5Z15F2A6`, `Z3Z6` precedent).
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
