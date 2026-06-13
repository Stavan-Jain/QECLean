# Phase 5 — gross `StabilizerCode 144 12` packaging: continuation plan

**Goal:** `grossStabilizerCode : StabilizerCode 144 12` + `HasCodeDistance
grossStabilizerCode 12` (conditional on the two engine Props
`LightStabilizerClassification`, `MImBound`), with the ≥6 bound unconditional.
User chose **full honest packaging** (no named structural Props).

## Status (this checkpoint)

`QEC/Stabilizer/Codes/BivariateBicycle/StabilizerCode.lean` compiles and is in
the umbrella. It contains:
- **§1** all offline-validated data: `dropSet`, `redP2`/`redCM` (reduced
  kernel bases), `phiX`/`phiZ` (decoders), `logX`/`logZ` (symplectic logicals).
- **§2** `d2term`/`cmTerm` sparse boundary forms, `decodeXAt`/`decodeZAt`,
  `kerCorrection`, and the two **proven** `native_decide` decoder identities
  `decoder_identity_X` / `decoder_identity_Z`. **This is the independence
  hard-core** — everything else is framework wiring.

Offline computation + validation: `compute2.py` → `data.json`; native_decide
feasibility proven (`Probe.lean`, passes ~5 s). All conventions in
[[bb-phase5-packaging]] memory.

## Remaining Lean construction (4 obligations)

### Obligation 2 — `generators_independent` (finish first; hard-core done)
Mirror toric `Toric/StabilizerCode.lean` §F (`rowsLinearIndependent_…`, lines
1229-1513) and its block kernel-collapse lemmas (`trimmed_combo_singleFace_…`).
1. Bridge `d2term f h j = grossComplex.boundary2 (Pi.single f 1) (h,j)` via
   `bbBoundary2_apply` + `conv_single_left_apply` (= `grossComplex.singleFace`).
   Likewise `cmTerm` vs `grossComplex.cutMap (singleVtx v)`.
2. Lift `decoder_identity_X` (basis form) to **all** `f` by linearity
   (`boundary1_apply_eq_sum`-style expansion): define `decodeX : (C1→ZMod2)
   →ₗ (C2→ZMod2)` from `phiX`; prove `decodeX (∂₂ f) + Σ_j f(dropSet j)•redP2_j
   = f`. Then `face_kernel_trivial : ∂₂ f = 0 ∧ (∀ d∈dropSet, f d=0) → f = 0`.
   Mirror for `vtx_kernel_trivial` (cutMap/decodeZ/redCM).
3. Define trimmed lists (66 vertex + 66 face stabs over `G \ dropSet`),
   `generatorsListPackaged` (length 132). Reduce `rowsLinearIndependent` via
   `Fintype.linearIndependent_iff` + the Z/X block split (X-rows zero on
   Z-half, Z-rows zero on X-half — `toSymplectic_{X,Z}Type_…`). Each block
   collapses to `{face,vtx}_kernel_trivial`. **No rank theorem needed.**

### Obligation 1 — closure equality (toric-analogous, ~easy)
For each `d ∈ dropSet`, `faceStabOf d ∈ closure(kept faces)`: the reduced
kernel vector `redP2 j` (with `∂₂ redP2_j = 0`, `native_decide`) gives
`∏_{f ∈ supp(redP2 j)} faceStabOf f = chainXOperator(∂₂ redP2_j) = 1`, and
`redP2_j(dropSet i)=[i=j]` isolates exactly `faceStabOf d`. Use
`chainXOperator_add` / `chainXOperator_boundary2_singleFace`. Mirror for
vertices via `chainZOperator_…`. Conclude `closure(generatorsListPackaged) =
grossComplex.homologicalStabilizerGroup.toSubgroup` (toric
`closure_packaged_eq_full`).

### Obligation 3 — 12 logical operators
For each `i : Fin 12`: `xOp = grossComplex.chainXOperator (indicator logX[i])`,
`zOp = grossComplex.chainZOperator (indicator logZ[i])`.
- `x_mem_centralizer` ← `chainXOperator_mem_centralizer_iff_mem_cycles`,
  i.e. `logX[i] ∈ cycles` (∂₁ = 0), `native_decide` via sparse `syndAt`-style.
- `z_mem_centralizer` ← `chainZOperator_mem_centralizer_iff_mem_dualCycles`
  (`dualBoundary logZ[i] = 0`).
- `anticommute (xOp,zOp)` ← `chainXOperator_commutes_chainZOperator_iff` is
  FALSE here ⇒ inner product `⟨logX[i],logZ[i]⟩ = 1`, `native_decide`.
- `logical_commute_cross` (i≠j): XX/ZZ commute by type; X_iZ_j commute ⇐
  `⟨logX[i],logZ[j]⟩ = 0` (i≠j). The full `12×12 = I` intersection matrix is
  one `native_decide` sweep. Non-triviality (`xOp_not_mem`) is FREE.
- centralizer is taken against the *packaged* group; use
  `centralizer_eq_of_toSubgroup_eq` + the obligation-1 subgroup equality.

### Obligation 4 — assemble + bridge
Build `grossStabilizerCode : StabilizerCode 144 12` (use
`grossComplex_numQubits : numQubits = 144`; `hk : 12 ≤ 144`). Expose
`grossStabilizerCode.toStabilizerGroup.toSubgroup =
grossComplex.homologicalStabilizerGroup.toSubgroup`. Then:
- `gross_logical_weight_ge_6` + bridge ⇒ unconditional ≥6 lower bound.
- `gross_pauli_distance_eq_12_of_engine hC hMim` (IsLeast … 12) + bridge ⇒
  `HasCodeDistance grossStabilizerCode 12` (min_weight from IsLeast.2,
  witness from IsLeast.1), via `IsNontrivialLogicalOperator_of_toSubgroup_eq`.
Finish: whole-repo `lake build`, `lean_verify` axiom audit of the
`HasCodeDistance` theorem, `/lean4:checkpoint`.

## Notes / gotchas
- `noncomputable def` for anything through `Subgroup.closure`.
- Keep data lines ≤99 chars (linter); regenerate via `gen_file.py` (wraps).
- Never run `lake build` while the lean-lsp MCP is live (olean race).
- `decoder_identity_*` build ~80 s total incl. data elaboration.
