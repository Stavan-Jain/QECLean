# bb_lab → QEC generators

Python scripts that emit (parts of) tracked Lean files under
`QEC/Stabilizer/Codes/BivariateBicycle/`. The Lean-side inventory (which
files are generated, class G/F/H taxonomy) lives in
`QEC/Stabilizer/Codes/BivariateBicycle/README.md`; this file is the
operational side.

**Environment**: `cd experiments/bb_lab && uv sync` (Python 3.11, deps in
`pyproject.toml`; dev group for pytest). Run generators as
`uv run python <script> [args]`.

**Clobber policy**: every generator that writes into `QEC/` must (a) emit the
`GENERATED FILE — DO NOT HAND-EDIT` banner naming itself, its data source and
the regen command, and (b) refuse to overwrite an existing target without
`--force` (pattern: `gen_pair72_packaging_data.py`). A hand-edit found in a
Class-G file is a bug: move the change into the generator and land generator +
regenerated output in the same PR.

## Live generators

| Script | Emits | Notes |
|---|---|---|
| `phase5/gen_file.py` | `Gross/StabilizerCode.lean` | **STALE — DO NOT RUN** (top-of-file warning in place): its template still emits the WIP skeleton and would clobber ~1,100 lines of hand-completed §2–§6 proofs. Queued rewrite: emit only a `Gross/StabilizerCodeData.lean` §1 data module with banner + `--force` guard |
| `scripts/gen_floor_lean.py` | `Gross/SafeFloor/MImFloorData.lean` | cost tables `D3V`/`RCELL` + Γ data |
| `scripts/gen_yrep_module.py <i>` | `Gross/SafeFloor/MImFloorY<i>.lean` | i ∈ {0,1,4,11,12}; per-orbit floor leaves |
| `scripts/gen_assembly_2d.py` | fragments for `Gross/SafeFloor/MImAssembly.lean` | Class F: paste between the `BEGIN/END GENERATED` markers only |
| `scripts/gen_pair72_packaging_data.py` | `Z3Z6/StabilizerCode.lean` | 15-check ALL-PASS validation gate + `--force` guard (the reference implementation); §1-data split queued |
| `scripts/gen_base_floor_lean.py` | `BaseFloors/<Name>.lean` | class-member small-cycle bundles (A15/T2) |
| `scripts/gen_f2a6_z5z30_data.py` | data feed for `Z5Z15F2A6/` | A17 line |

## Retired (`scripts/attic/`)

| Script | Why retired |
|---|---|
| `attic/gen_orbit_module.py` | emitted `MImFloorO*` modules that no longer exist (superseded by the Y-representative transport + `gen_yrep_module.py`) |
| `attic/gen_assembly.py` | emitted the 13-orbit `MImAssembly` (superseded by the 5-orbit 2-D dispatch, `gen_assembly_2d.py`) |
