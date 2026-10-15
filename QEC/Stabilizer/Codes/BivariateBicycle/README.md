# BivariateBicycle — orientation (read me before editing)

Every bivariate-bicycle **instance** lives in its own subdirectory with a
sibling umbrella `.lean`; the shared theory lives in
`Framework/Homological/BB*` (`BBChainComplex`, `BBCover`, `BBDoubling`,
`BBDeckTower`, `BBBocksteinRank`, `BBEpsFree*`, `BBSmallCycle`,
`BBDeficitWall`, `BBSeamBZ`) together with the instance-agnostic certificate
layer `F2Mask` + `BZCertificate`. This README is the task router and status
board; the per-module one-liner map lives in the umbrella docstring
(`Gross.lean`).

## Instances

| Dir | Code | Distance status |
|---|---|---|
| `Gross/` | gross `[[144,12,12]]` (base `[[72,12,6]]`) | **d = 12 unconditional, kernel-only** — axioms are exactly `propext`, `Classical.choice`, `Quot.sound`; no `native_decide`, no `sorry` (proved through the generic doubling layer and packaged by `Gross/Distance.lean`) |

The other instances (`Z3Z6/`, `Z5Z15F2A6/`, `BaseFloors/`) are parked — see
"Parked instances" below.

## Task router

- **Understand the gross d = 12 proof**: read `Gross.lean`'s docstring, then
  the spine in umbrella order (Defs → CoverTransfer → DeckHomotopy → Witness →
  Assembly → BaseDistance → DangerousSector → SafeSector → StabilizerCode →
  SeamBZ → LayerInstance → Distance). Paper version (whose safe floor is the
  older CRT-engine argument): `qec-lab:docs/gross-distance-proof.md`.
- **The certificate layer** (safe floor + light-boundary census by
  Brouwer–Zimmermann): `Framework/Homological/BBSeamBZ.lean` (generic
  statement), `Gross/SeamBZ.lean` (the gross certificate).
- **Regenerate a table / change generated data**: see the generated-files
  table below and `qec-lab:experiments/bb_lab/GENERATORS.md`. Never hand-edit a
  Class-G file.
- **Add a new instance**: follow "Adding an instance" below.
- **Change the doubling layer itself**: `Framework/Homological/BBDoubling.lean`
  (not this directory); its per-instance inputs are documented there.

## Generic doubling route

`CoverTransfer.lean` defines the canonical `grossCoverData` before the distance
proofs. `BaseDistance` instantiates `SmallCycleData`; `DeckHomotopy` supplies
`P = 0`, `Q = (1 + x²) ⋆ B` to the generic Bézout theorem; `DangerousSector`
uses the generic single/pair logical-floor rungs with Gross shape certificates;
`SafeSector` identifies `MImBound` with `SeamCosetFloor 12` and invokes the
generic reduction; `SeamBZ` discharges `MImBound` and the light-boundary
classification from one generic `SeamBZCertificate`. `Assembly` retains the old
conditional names as wrappers.
`LayerInstance` proves the unconditional distances
(`gross_{chain,pauli}_distance_eq_12`) as one application each of the packaged
Doubling theorem (`chain/pauli_distance_eq_double_of_admissible`), whose
dangerous-sector input is the generic dispatch `dangerousFloorNZ_of_admissible`:
the census makes every light boundary `LightBoundaryAdmissible` (hexagons:
single shape, `t = 3`; D-pairs: pair shape, `t = 1`;
`lightBoundaryAdmissible_of_classification` in `DangerousSector`). `Distance`
packages the Pauli-distance result through `has_code_distance_of_isLeast`.

After building, `lake env lean scripts/BBDoublingCheck.lean` verifies a separate
four-qubit cover and checks that both conditional and unconditional Gross
capstones depend on the generic base, homotopy, rung, sector, and
Brouwer–Zimmermann certificate theorems — the unconditional ones through the
packaged Doubling theorem and the admissible dispatch, not through the
per-instance `dangerous_sector_of_classification`.

## Hypothesis-discharge map (gross)

| Named hypothesis | Discharged by | Grade |
|---|---|---|
| `BaseDistanceGe6` | `Gross/BaseDistance.lean` (`SmallCycleData` instance) | kernel `decide` + analytic |
| `LightStabilizerClassification` | `Gross/SeamBZ.lean` (`GrossBZ.lightStabilizerClassification_bz`: the certificate's light-boundary census, 252 boundaries = 36 hexagons + 216 D-pairs) | kernel `decide` |
| `DangerousSectorGe12` | `Gross/DangerousSector.lean` ((M), generic logical-floor rungs: the capstones take it from the generic admissible dispatch via `lightBoundaryAdmissible_of_classification`; the per-instance assembly `dangerous_sector_of_classification` remains for the conditional engine route) | analytic + kernel `decide` |
| `SafeSectorGe12` → `MImBound` | `Gross/SafeSector.lean` (generic Smith-coset reduction) | analytic |
| `MImBound` | `Gross/SeamBZ.lean` (`GrossBZ.mimBound_bz`: `SeamBZCertificate.seamCosetFloor` at 11 over all 63 Smith classes at once, lifted to 12 by parity) | kernel `decide` (two BZ walks, 510 414 words) |
| capstones | `Gross/Distance.lean` (`grossStabilizerCode_hasCodeDistance_12_uncond`, `grossStabilizerCodeWithDistance`) + `Gross/LayerInstance.lean` (`gross_chain/pauli_distance_eq_12`, one application each of the packaged Doubling theorem `chain/pauli_distance_eq_double_of_admissible`) | — |

The Z3Z6 (pair72, `[[36,4,4]] → [[72,4,8]]`) and Z5Z15F2A6
(`[[150,8,8]] → [[300,8,16]]`) instances, which used to mirror this map, are
**parked on branch `claude/z3z6-parked`** pending de-nativization — see
"Parked instances" below.

## How the certificates are checked (2026-10-14)

The gross `d = 12` cone contains **zero `native_decide`**: every leaf is a kernel
`decide` (mostly `decide +kernel`) or an analytic proof, so the capstones carry
only mathlib's three axioms. This is not an achievement local to `Gross/` — it is
the repo-wide bar: everything on `main` must print exactly
`[propext, Classical.choice, Quot.sound]`. See CLAUDE.md § "Axiom policy", and
park rather than merge anything that cannot meet it.

Both per-instance floors come from **one Brouwer–Zimmermann certificate** of the
generic shape `XDoubleCoverData.SeamBZCertificate` (`BBSeamBZ.lean`). The coset
code `K = seamC (ker ∂₂) + im ∂₂` (dimension 36 in `𝔽₂⁷²`) is given by 42
generator words packed into `Nat` masks, the seam generators tagged above bit 72
by their `ker ∂₂` coordinates. Two disjoint information sets of `K` are walked
to depth 5 and 4; since every word of weight `≤ 10` has at most 5 (resp. 4)
pivots set in one of them, the walks visit every such word and check that it is
heavy, or untagged and a listed light boundary. That single check yields both
`SeamCosetFloor 11` (hence `12` by parity) and the light-boundary census. The
`ker ∂₂` basis is certified by a 30-step peeling order (`kernel_eq_sum_of_peel`).

Kernel-cost notes that mattered: the walk predicates use raw `Nat.*` functions
rather than `>>>`/`&&&`/`decide (· ≤ ·)` (the notation's instance unfolding
was 4× the GMP work), the popcount is a byte table, and `xor_walk_decide₂` splits
each walk into one `decide +kernel` per pair of first rows so each kernel cache
stays small. The walks take ~80 s; nothing in the gross cone needs more than
~0.7 GB above the import baseline. The retired CRT-engine route (`CRTFrame`,
`LightStab`, `LightStabClassify`, `SafeFloor/`, ~6.5k lines) is in git history.

The certificate statement is instance-agnostic; a new cover instance supplies
only its mask encoding, `ker ∂₂` basis, generator words, windows and walks
(generated data), plus the sparse forms of its `∂₂` and `seamC`.

## Parked instances

`main` is being driven to a `native_decide`-free state, so every instance that
still carried one has been removed from this tree and lives on branch
**`claude/z3z6-parked`**:

| Parked | Result given up | `native_decide` |
|---|---|---|
| `Z3Z6/` (pair72, `[[36,4,4]] → [[72,4,8]]`, d = 8 unconditional) | `pair72_*_distance_eq_8` | 42, five of them `2^18` sweeps that dominated a whole-repo build |
| `Z5Z15F2A6/` (`[[150,8,8]] → [[300,8,16]]`, d = 16 unconditional) | `cover300_chain/pauli_distance_eq_16` | 101 native leaves (the a15/a17 discharge engine — see the branch's `PARKED-NATIVE-DECIDE.md`) |
| `BaseFloors/` (BB90, BB108, Z6Z14) | three certified `BBSmallCycle` class members | 12 (`epsA/epsB/check_two/check_four` ×3 files) |

`Z3Z6/PARKED.md` on that branch records the Z3Z6 rationale in detail, and the
branch's root `PARKED-NATIVE-DECIDE.md` covers the rest — including the
2026-08-27 refresh that brought `Z5Z15F2A6/` to its unconditional a15 state
(`e6f03ad`: all three floor hypotheses discharged as kernel-checked theorems)
together with the `Framework/Homological/{BBCoverTranslate,BBDoubling}`
extensions it depends on. All three are clean leaves in this tree — nothing
outside each directory imported its declarations — so restoring one means
re-adding the directory, its sibling umbrella, the import line in
`BivariateBicycle.lean`, the rows removed from this README, and (for
`Z5Z15F2A6/`) porting those two framework companions.

The abstract machinery they exercised stays in this tree:
`Framework/Homological/BBSmallCycle.lean` (the A15/A16 class small-cycle
theorem) and `BBDoubling`/`BBCover` are untouched — they simply have no
concrete instance here besides `Gross/`.

## Generated files (Class G: fully generated — NEVER hand-edit)

| File | Generator (`qec-lab:experiments/bb_lab/`) | Data |
|---|---|---|
| `Gross/StabilizerCodeData.lean` | `phase5/gen_file.py` (`--force` guard; emits data only) | `phase5/data.json` |
| `Gross/SeamBZData.lean` | `scripts/gen_gross_bz.py` (`--emit [--force]`; validates every certificate, including both walks, in Python before writing) | computed from the code |

There are no Class F files (generated fragments between
`-- BEGIN/END GENERATED` markers) left in this tree. Everything else is Class H (hand-maintained;
may embed machine-*validated* data). Rule: **a hand-edit to a Class-G file is
a bug — change the generator (in the qec-lab companion repo) and regenerate,
landing both repos' changes together.** Generators run from a sibling qec-lab
checkout and write here via `QECLEAN_ROOT` (default `../QECLean`). Operational
details (env, clobber guards, stale generators): `qec-lab:experiments/bb_lab/GENERATORS.md`.

## Edit rules

1. New module ⟹ `import` line in the NEAREST umbrella (`Gross.lean`,
   `<Instance>.lean`) — then run
   `bash scripts/check-umbrellas.sh` (orphan modules silently don't build).
2. Class-G files: regenerate, never edit (banner at the top of each).
3. `native_decide`, `sorry`, and custom axioms are forbidden on `main`;
   validate with `lake env lean scripts/AxiomCheck.lean`. No
   `set_option linter.* false` suppressions.
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
   `SeamBZData.lean` + `SeamBZWalk.lean` + `SeamBZ.lean` (a
   `SeamBZCertificate`, generated by a clone of `gen_gross_bz.py`) →
   `Distance.lean` (capstone) → `StabilizerCodeData.lean` +
   `StabilizerCode.lean` (via a generator clone with validation gate +
   `--force` guard).
3. Discharge the `BBDoubling` inputs by name: `LogicalFloor` (or derive it
   from `StrongBaseFloor`), `DeckTrivialOnH1`, `DangerousFloorNZ`,
   `SeamCosetFloor`, and a tight witness whose pullback is not a boundary.
   `SeamBZCertificate.seamCosetFloor` gives `SeamCosetFloor`, and
   `SeamBZCertificate.boundary_census` the light-boundary list the dangerous
   rungs dispatch over — the walk size is what limits this to small bases
   (gross: 510 414 words; the A28 notes price larger bases at 10⁹+). Show
   each light boundary of the census `LightBoundaryAdmissible` (single shape,
   pair shape, or `t = 1` window) and conclude with the packaged Doubling
   theorem `pauli_distance_eq_double_of_admissible`, which runs
   `dangerousFloorNZ_of_admissible` and `safeFloor_of_seamCosetFloor` for the
   sector reductions (the `..._of_logicalFloor` assemblies remain available
   for floors proved some other way).
   `StrongBaseFloor` is unsuitable for weight-six-generator codes with base
   distance above six.
4. Wire umbrellas (rule 1); add the instance row to the table above and, if
   generators are involved, rows in the generated-files table + GENERATORS.md.

## Staleness contract

Any PR that adds/moves/renames a module here, changes how a floor is
certified, changes a generator, or adds an instance MUST update this README (the tables
are keyed by stable names — that is the anti-staleness design). A PR touching
`BivariateBicycle/**` structure without touching this file is suspect.
