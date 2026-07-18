# S3.9 — `StabilizerCodeWithDistance 72 4 8` packaging plan

> **✅ DONE (2026-07-02).** All three stages executed as planned:
> `gen_pair72_packaging_data.py` (Stage A, 15-check ALL-PASS gate),
> `Z3Z6/StabilizerCode.lean` (Stage B, §1–§6 + the bundle
> `pair72StabilizerCodeWithDistance : StabilizerCodeWithDistance 72 4 8`),
> umbrella + docs (Stage C).  Verified: LSP zero-error, `lake build` green,
> axiom audit = standard three + `native_decide` oracles (no `sorry`).
> Two deviations from the plan text: the face and vertex drop-sets
> coincided (`[(0,0),(0,1)]`), so the single-`dropSet` gross template
> applied verbatim; and §3–§6 were produced by scripted transformation
> of the gross file (renames + 6→2/12→4 constant fixes) rather than
> hand-adaptation — only the §6 tail (distance transport with the
> ∃-restatement, the `WithDistance` bundle) is new text.

The one remaining gap from the PR #53 stage-4 wrap (`A_HANDOFF.md` A9 update):
the `[[36,4,4]] → [[72,4,8]]` doubling instance is proven at the chain and
Pauli levels (`Z3Z6/Distance.lean`: `pair72_chain_distance_eq_8`,
`pair72_pauli_distance_eq_8`, gross axiom bar), but is not yet packaged as a
first-class `StabilizerCode` / `StabilizerCodeWithDistance` object.

**Goal:** `pair72StabilizerCodeWithDistance : StabilizerCodeWithDistance 72 4 8`
in a new `QEC/Stabilizer/Codes/BivariateBicycle/Z3Z6/StabilizerCode.lean`,
axiom bar unchanged (standard three + `Lean.ofReduceBool`).

**Model:** the gross Phase-5 packaging
(`QEC/Stabilizer/Codes/BivariateBicycle/Gross/StabilizerCode.lean`, §1–§6, plus
`experiments/bb_lab/phase5/PLAN.md` as the design record and
`MImAssembly.lean` §end for the final bundle). Everything below is that file
re-instantiated at the pair72 scale, which is much smaller: 2-dim kernels
(vs 6), 4 logical qubits (vs 12), 36 group cells (vs 72).

## Stage A — offline data generation (bb_lab, Python)

New script `experiments/bb_lab/scripts/gen_pair72_packaging_data.py`, adapted
from `phase5/compute2.py` + `phase5/gen_file.py` (gross) with the pair72
parameters from `gen_pair72_z6z6_data.py` — cover group `Z6×Z6`,
`A = x² + y + y³`, `B = 1 + x + y²`. **Mind the convention bridge:
repo-left = lab-right** (`Z3Z6/Defs.lean` header). Emit + validate:

1. `dropSet` — 2 faces + 2 vertices to trim the natural 72 generators
   (36 face + 36 vertex stabs) down to 68 = n − k. (`dim ker ∂₂ = 2` per the
   A9 screen; `dim ker cutMap = 2` dually — script must confirm both.)
2. `redP2` / `redCM` — reduced bases of `ker ∂₂` / `ker cutMap` (2 each),
   normalized so `redP2 j (dropSet i) = [i = j]` (closure relations AND
   independence kernel-collapse in one object).
3. `phiX` / `phiZ` — syndrome-decoder left-inverse certificates for the 34
   kept face rows / 34 kept vertex rows (no rank theorem).
4. `logX` / `logZ` — symplectic basis: 4 X-cycles + 4 Z-dual-cycles with
   identity 4×4 intersection matrix.
5. In-script validation of every identity the Lean file will `native_decide`
   (decoder identities, kernel-basis facts, cycle/dual-cycle conditions,
   intersection matrix), ALL-PASS gate, then emit Lean literals.

Note `experiments/bb_lab/data/` is gitignored — the JSON is regenerable, the
Lean literals are the durable artifact.

## Stage B — the Lean instance file

`QEC/Stabilizer/Codes/BivariateBicycle/Z3Z6/StabilizerCode.lean`, mirroring
gross §1–§6 with `pair72Complex` / `G72` in place of `grossComplex` /
`GrossGroup`:

- **§1** data literals (Stage A output) over `G72 = ZMod 6 × ZMod 6`.
- **§2** sparse boundary terms `d2term`/`cmTerm`, `decodeXAt`/`decodeZAt`,
  `kerCorrection`, and the two decoder identities (`native_decide`; try plain
  `decide` first — 36-cell sweeps may be cheap enough per the
  native_decide→decide swap rule).
- **§3** kernel-trivial cores `face_kernel_trivial` / `vtx_kernel_trivial` —
  the gross proofs are polynomial-agnostic modulo names; adapt near-verbatim.
- **§4** closure equality: per-drop closure relations from `redP2`/`redCM`
  (`keptCoords`, `keptPartX/Z`, `closure_packaged_eq`).
- **§5** symplectic-row bridges + block-split `rowsLinearIndependent` →
  `generators_independent_packaged`. Arithmetic: `keptCoords.length = 34`,
  packaged list length 68 = 72 − 4.
- **§6** `packagedSG`, 4 `logicalQubit`s, assembly:
  - **Use the abstract-chain-helper pattern** (gross §6 header): every
    centralizer / (anti)commutation fact proven with the chain held abstract,
    `logicalQubit` only applies them — this is the known fix for the kernel
    whnf runaway.
  - `pair72StabilizerCode : StabilizerCode pair72Complex.numQubits 4`.
  - `pair72StabilizerCode_toSubgroup_eq` bridge (closure of trimmed list =
    `pair72Complex.homologicalStabilizerGroup.toSubgroup`).
  - Transport `pair72_pauli_distance_eq_8` through
    `IsNontrivialLogicalOperator_of_toSubgroup_eq` — same proof shape as
    `grossStabilizerCode_hasCodeDistance_12`, but **unconditional from the
    start** (no engine Props) → `HasCodeDistance pair72StabilizerCode 8`.
  - Bundle: `pair72StabilizerCodeWithDistance : StabilizerCodeWithDistance
    72 4 8` (check `pair72Complex.numQubits` reduces defeq to 72 as
    `grossComplex.numQubits` did to 144; else insert the
    `pair72Complex_numQubits` cast).

**Considered and deferred:** factoring a *parametric* packaging layer into
`Framework/Homological/BBDoubling.lean` (drop sets / decoders / logicals as
bundle fields). The data is instance-specific and the generic parts (§3 shape,
§6 helpers) already live as `HomologicalCode` lemmas; parametrization pays off
at the third instance (the hit3/4/6 `[[144,12,12]]` gross twins). Do the
direct instantiation now; revisit when the engine-frame targets land.

## Stage C — wiring, docs, verification

1. Import the new module in the `Z3Z6.lean` umbrella (orphan-module trap).
2. Docs: `BivariateBicycle.lean` header, `A_HANDOFF.md` A9 block
   ("packaging pending" → done), `pipeline/research_log.md` entry,
   `docs/gross-distance-extensibility.md` §5 status line.
3. Verify: lean-lsp MCP diagnostics per file while iterating; ONE `lake build`
   at the end; `lean_verify` axiom audit on `pair72StabilizerCodeWithDistance`
   (expect standard three + `ofReduceBool`, no `sorryAx`).

## Ops notes

- Worktree mathlib share is already symlinked (manifests match).
- Never two lake processes; MCP and `lake build` share the workspace lock.
- Gross §5/§6 needed `set_option maxRecDepth 4096` and one
  `maxHeartbeats 1000000` — expect smaller or no bumps at 72 qubits, but the
  same knobs apply (comment placement rule: after `... in`).
