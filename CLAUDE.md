# CLAUDE.md — agent orientation

This is a Lean 4 / mathlib formalization of the stabilizer formalism for
quantum error correction. The active math is in `QEC/`. Build with `lake build`.

## Project tour

```
QEC/
├── Foundations/         # Hilbert spaces, vectors, gates, tensor product
├── RepetitionCode/      # Classical repetition code recovery (older module)
└── Stabilizer/          # Main formalization
    ├── PauliGroupSingle/    # Single-qubit Pauli operators (X, Y, Z, I, phases)
    ├── PauliGroup/          # n-qubit Pauli group + commutation theory
    ├── BinarySymplectic/    # Symplectic representation, check matrices
    ├── Core/                # StabilizerGroup, Codespace, Centralizer,
    │                        # LogicalGates, CSS, CodeDistance abstractions
    ├── Codes/               # Concrete codes: Shor9, Steane7, Repetition*,
    │                        # Toric*, RotatedSurface3, QuantumHamming
    └── Lattice/             # Toric code lattice geometry, chains,
                             # boundary maps, homology, H¹ dimension
```

Top-level umbrella `.lean` files (e.g. `QEC/Stabilizer/Stabilizer.lean`,
`Codes.lean`, `Lattice.lean`) just re-export submodules — don't put real
content there.

## Naming and style conventions

- **Lemmas / theorems**: `snake_case`. Use `theorem` for top-level results,
  `lemma` for stepping stones.
- **Definitions**: `camelCase` (`stabilizerSum`, `mulOp`, `phasePower`,
  `toMatrix`).
- **Namespaces**: math sits under `Quantum`; type-bound lemmas sit under
  the type's namespace (`NQubitPauliGroupElement.commutes_iff_*`).
- **`noncomputable def`**: required for any def whose RHS uses
  `Subgroup.closure` or transitively goes through `NQubitPauliGroupElement.instGroup`
  (mathlib's `Group` instance on this type is noncomputable as of v4.30).
  Common pattern: every concrete code's `def subgroup` and
  `mkStabilizerFromGenerators` / `toStabilizerGroup` in `StabilizerCode.lean`.
- **Tactics**:
  - `simp +decide` is preferred over hand-written `decide` (and avoids the
    "expected type must not contain free variables" trap).
  - `native_decide` is allowed (per user preference).
  - When closing residual `if c then 1 else 0`-style goals after `simp`,
    `split_ifs <;> simp_all (config := {decide := true}) <;> first | rfl |
    exact absurd rfl ‹_›` is the common closer.
  - **Probing residual goals**: prefer the `lean_goal` MCP tool (see "Agent
    tooling" below) — it returns the live `goals_before` / `goals_after` at
    a position without any edit or rebuild. Fallback when the MCP isn't
    available: replace the failing tactic tail with `(try sorry)` and
    rebuild; the "declaration uses sorry" warning includes the residual
    goal state.
  - **`Finset.card` of `{a, b, c, d}` with all-pairwise-distinct hypotheses**:
    `simp_all +decide [Finset.filter_eq', Finset.filter_or,
    Finset.card_insert_of_notMem, Finset.mem_insert, Finset.mem_singleton]`
    — as of mathlib v4.30 `simp_all` picks up the `Ne` hypotheses (in both
    directions) from context automatically. The older guidance to pass
    `h₁, h₂.symm, …` explicitly is stale and now triggers
    `linter.unusedSimpArgs`.
  - **`simp_all` with bidirectional hypotheses can erase what you need**:
    if a hypothesis is a `↔` like `hfilt_eq : P ↔ Q`, `simp_all` may rewrite
    `Q` back to `P` in a subgoal you wanted to keep simplified. Workaround:
    `clear hfilt_eq` (or rename to a one-shot `have`) before `simp_all`.
- **Sorry markers**: `sorry  -- TODO(<short-tag>): <one-line note about goal shape>`.
  Always tag so the next session can grep for them.

## Linter policy

**No `set_option linter.* false` suppressions in the codebase.** Every
warning is either fixed cleanly or left visible. Don't reach for
`set_option linter.X false in` even on tricky proofs — restructure, or
accept the visible warning and document it as out-of-scope.

The only category currently treated as out-of-scope is `linter.flexible`
on the toric `Lattice/` and `Codes/` proofs (the `simp_all +decide [...]`
/ `simp +decide [...]` family). Don't introduce new sites; existing ones
will be cleaned up in a dedicated batch via the MCP union trick above.

## Linter-clean idioms

Codebase-wide style as of v4.30 (each is enforced by a corresponding
mathlib linter; don't introduce new violations):

- **`push Not at h`** instead of `push_neg at h`.
- **`refine` with `?_` placeholders** instead of `refine'` with `_`. If
  the goal is the structure-builder shorthand `refine { .. }` and `refine`
  can't infer the field metavars, spell the fields explicitly:
  `refine { toFun := ?_, map_add' := ?_, map_smul' := ?_ }`.
- **`induction k with | zero => ... | succ k ih => ...`** instead of
  `induction' k with k ih`. For closure-style induction, name cases by
  the actual principle:
  - `Subgroup.closure_induction`: `| mem g hg | one | mul x y hx hy ihx ihy | inv x hx ih`
  - `Finset.induction`: `| empty | insert a s has ih`
- **`change G`** instead of `show G` when the tactic actually rewrites
  the goal (defeq but not syntactically equal). `show` is reserved for
  readability annotations where the displayed term matches the goal up
  to alpha-equivalence.
- **`set_option maxHeartbeats N in`** must be followed by a `--` comment
  explaining why, **AFTER `... in` and BEFORE the declaration**:
  ```lean
  set_option maxHeartbeats N in
  -- why this bump is needed
  /-- doc -/
  theorem ...
  ```
  Comments placed before `set_option` don't satisfy
  `linter.style.maxHeartbeats`. The same ordering rule applies to
  `omit [Fact ...] in`: the doc-comment must come AFTER `... in`, or the
  parser rejects the intervening doc-comment.

## Project-specific helpers (NOT mathlib)

These are local to this codebase — search here before assuming mathlib has them:

- `NQubitPauliGroupElement.toMatrix`, `.mulOp`, `.phasePower`, `.operators`
- `NQubitPauliGroupElement.Anticommute`, `.anticommutesAt`
- `NQubitPauliGroupElement.commutes_iff_even_anticommutes` — main parity-based
  commutation lemma for general Paulis (the "count of anticommuting qubits is
  even" characterization)
- `StabilizerGroup`, `.toSubgroup`, `.is_abelian`, `.one_mem`,
  `.neg_identity_not_mem`, `.codespaceSubmodule`
- `IsNontrivialLogicalOperator` has **three** conditions (see
  `IsNontrivialLogicalOperator_iff`): in centralizer, not in subgroup, AND
  `∀ s ∈ S.toSubgroup, s.operators ≠ g.operators`. The third is easy to forget;
  it's what makes CSS-bridge arguments like `not_both_boundary_of_nontrivial`
  work (`g_X * g_Z` has the same operator part as `g`, so it can't be in the
  stabilizer).
- `IsNontrivialLogicalOperator_of_toSubgroup_eq` — translates the predicate
  between two stabilizer groups with the same `toSubgroup`. Used to convert
  `HasToricDistance`-style proofs (against `stabilizerGroup L`) into
  `HasCodeDistance`-style proofs (against `(toricStabilizerCode L).toStabilizerGroup`).
- `IsStabilizedBy`, `IsStabilizedVec`, `IsInCodespace`, `PreservesCodespaceConjugation`
- `NQubitVec`, `Vector` (= `α → ℂ`), `NQubitBasis`
- `Stabilizer.Lattice.rowMajor_injective`, `fin_ne_of_val_lt_offset_le`
- `EdgeIdx`, `FaceIdx`, `VtxIdx`, `C0`/`C1`/`C2` chains, `next`/`prev`,
  `zeroCoord`, `hEdge`/`vEdge`/`hEdgeIdx`/`vEdgeIdx`, `singleFace`, `singleVtx`
- `Stabilizer.Lattice.eq_prev_iff_next_eq` (and `.next_prev`, `.prev_next`,
  `.next_ne_self`, `.prev_ne_self`) — use these instead of unfolding `next`/`prev`
  to raw `(i + 1) % L` / `(i + L - 1) % L`; `omega` chokes on the modular
  arithmetic, but the symbolic lemmas dodge it.
- `toricCycles`, `toricBoundaries`, `toricBoundary1`/`toricBoundary2`,
  `toricDualCycles`, `toricDualBoundaries`
- `toricXOperatorOfChain`, `toricZOperatorOfChain` (and `_add`, `_zero` for
  homomorphism); `toricVertexCutMap` (LinearMap C0 → C1)
- `toricZOperatorOfChain_cutMap_singleVtx` /
  `toricXOperatorOfChain_boundary_singleFace` — bridges single-stab vertex/face
  ops to chain operators; key inputs for any homological identity proof.

## Build & verification

```
lake build                                    # whole repo (~10 min cold)
lake build QEC.Stabilizer.Core.Codespace      # one module
lake env lean /tmp/probe.lean                 # one-off file check
```

Always verify with `lake build` before claiming a fix works. The error
output prints the residual goal under each failure — read it before guessing
tactics.

## Worktrees: reuse the main repo's prebuilt mathlib

Fresh worktrees under `.claude/worktrees/<name>/` start with no
`.lake/packages/`, so the first `lake build` triggers a full mathlib
clone + rebuild (multiple gigabytes, ~30+ minutes, and holds the
workspace lock the whole time). The main repo at the worktree's
grandparent already has mathlib cloned and built — share it via
symlink before the first build:

```bash
# From the worktree root (e.g. .claude/worktrees/<name>/):
diff lake-manifest.json ../../../lake-manifest.json && {
  rm -rf .lake/packages
  ln -s ../../../../.lake/packages .lake/packages
}
```

The `diff` guards against bumping mathlib on the worktree branch and
silently using main's stale build. If the manifests differ, do **not**
symlink — `lake exe cache get` is the right fix, but it's on the
require-permission list (see below) so **ask the user first**.

The worktree's own `.lake/build/` stays separate — only the immutable
dependency artifacts under `.lake/packages/<pkg>/.lake/build/` are
shared, so there's no risk of cross-worktree contamination.

If `lake build` was already invoked and is partway through cloning
mathlib, killing it leaves `.lake/packages/mathlib/` in a half-cloned
state (just a `.git/` directory). `rm -rf .lake/packages` cleans it up,
then symlink as above.

## Agent tooling: lean-lsp MCP

This repo ships a project-scoped MCP server in `.mcp.json`
(`uvx lean-lsp-mcp`, from [oOo0oOo/lean-lsp-mcp](https://github.com/oOo0oOo/lean-lsp-mcp)).
Claude Code prompts to approve it on first launch. Once approved, the agent
gets live LSP access — proof states, diagnostics, hover docs, mathlib
search, multi-tactic attempts — without round-tripping through `lake build`.

**Prefer these MCP tools over the documented fallbacks elsewhere in this file:**

- `lean_goal` — proof state at a `(file, line[, column])`. Use instead of
  the `(try sorry)` rebuild trick.
- `lean_diagnostic_messages` — errors/warnings/sorries with severity filter.
  Use instead of greping build logs.
- `lean_multi_attempt` — try several tactics at one position in a single
  call. Use instead of the edit / `lake build` / repeat loop when probing
  candidate closers.
  - **`linter.flexible` union trick**: at a flagged `<;> simp_all +decide`
    site, call `lean_multi_attempt` with `["simp_all? +decide"]`. Lean
    prints separate `simp_all +decide only [...]` suggestions for each
    sibling subgoal. Take the **union** of all the suggested lemma lists
    and use it as one explicit replacement — closes the goals simp would
    close and leaves the others in the exact same form the trailing
    bullets/exact-tactics need. Same pattern with `simp? +decide` for the
    non-`_all` variant. This is the only reliable way to retire
    `linter.flexible` warnings on broadcast-tactic-heavy proofs without
    breaking the downstream tactics.
- `lean_loogle`, `lean_leansearch`, `lean_leanfinder`, `lean_state_search`,
  `lean_hammer_premise` — mathlib lemma discovery. Use **before** guessing
  names, especially for the v4.30 API-drift cases listed below.
- `lean_hover_info`, `lean_declaration_file` — confirm the current mathlib
  API at a symbol (rename- and deprecation-safe).
- `lean_local_search` — ripgrep over project + stdlib, scoped by the LSP.

**Caveats for this repo:**

- The MCP's LSP shares the workspace lock with `lake build` (see "Never
  run two lake processes concurrently" below). Don't fire off a parallel
  build while it's serving.
- External search tools rate-limit to 3 requests / 30s. Batch queries.
- The MCP **does not edit files**. Use the Edit tool to apply tactics that
  `lean_multi_attempt` validated.
- If the LSP fails to start under the MCP, `bash scripts/prune-stale-ileans.sh`
  is the right first move — same root cause as an editor crash.

### Lean REPL (fallback, when MCP is unavailable)

If the MCP server is down, the raw Lean REPL still works
(`leanprover-community/repl`). Clone it, `lake build`, drive with JSON
per its README.

## Forbidden / require-permission actions

**Never run these without asking the user first, every time:**

- `lake exe cache get` / `lake exe cache get!`
- `lake update`
- `rm -rf ~/.cache/mathlib`
- Any other operation that re-downloads or rebuilds large fractions of mathlib

These take 5–30+ minutes, hold the workspace lock (blocking everything else),
and have caused real corruption when run concurrently with other lake
processes. Verify alleged corruption with a cheap probe first
(`echo 'import That.Module' > /tmp/p.lean && lake env lean /tmp/p.lean`)
before reaching for the heavy hammer.

**Never run two lake processes concurrently.** They share a workspace lock
and partial writes can corrupt build artifacts (we've seen "Foo 2.ilean"
duplicates and silent olean truncation from this).

## When the Lean LSP fails to start

Run `bash scripts/prune-stale-ileans.sh`. This handles the four classes of
stale build artifacts that crash `lake serve`:

0. macOS-style duplicates (`Foo 2.ilean`)
1. Orphan ileans (source `.lean` no longer exists)
2. Stub ileans (no `decls` field — deprecation/umbrella modules)
3. Old-format ileans (reference usage tuples not length 4 or 5)

If you're upgrading the toolchain, see `TOOLCHAIN_UPGRADE.md` (gitignored,
local runbook).

## Things that broke recently in v4.30 (be aware)

- `Subgroup.normalizer` takes `Set G`, not `Subgroup G` — no dot notation.
  Write `Subgroup.normalizer S.toSubgroup` not `S.toSubgroup.normalizer`.
- `simp [ZMod, ← even_iff_two_dvd]` no longer turns `(c : ZMod 2) = 0` into
  `Even c`. Use `Finset.sum_boole` + `ZMod.natCast_eq_zero_iff_even` instead.
- `Matrix.mulVec_smul` rewrites can fail to unify when scalar type and
  matrix-entry type differ (`ℝ` vs `ℂ`). Workaround: wrap in an explicit
  `show ∀ (M : Matrix _ _ ℂ) (b : ℝ) (w : NQubitVec n), M.mulVec (b • w) =
  b • M.mulVec w from fun _ _ _ => Matrix.mulVec_smul _ _ _`.
- `push_neg` is deprecated — prefer `push Not`.
- mathlib's `Matrix.mul_eq_one_comm`, `Matrix.isUnit_of_right_inverse` are
  deprecated; use `mul_eq_one_comm` and `IsUnit.of_mul_eq_one`.
  **Signature gotcha**: `IsUnit.of_mul_eq_one` is `(b : M) (h : a * b = 1)`
  — the right-hand operand is explicit. For a square `h_mul : M * M = 1`
  write `IsUnit.of_mul_eq_one M h_mul`, not `IsUnit.of_mul_eq_one h_mul`.
- `Finset.filter_union_filter_neg_eq` → `Finset.filter_union_filter_not_eq`
  (`neg` → `not`). Same renaming on `Finset.disjoint_filter_filter_neg` →
  `Finset.disjoint_filter_filter_not`.
- `Nat.xor_cancel_left` / `Nat.xor_cancel_right` don't exist under those
  names — they're in Batteries as `Nat.xor_xor_cancel_left` /
  `Nat.xor_xor_cancel_right` (note the extra `xor_`). Used in
  `QuantumHamming.lean`'s involution proof.
- `Prod.mk.inj_iff` is gone — use `Prod.mk_inj`.
- `((List.finRange L).product (List.finRange L)).length = L * L` doesn't
  reduce by `simp` directly. Workaround: `unfold List.product; simp [List.length_flatMap]`.
- The `List.countP_eq_count_of_decide_iff`, `List.countP_add_countP_eq_length`,
  `List.length_filter_eq_countP` family doesn't exist (or moved). For
  `(L.filter p).length` arithmetic, route through `List.toFinset_card_of_nodup`
  (when the list is `Nodup`) and `Finset.card_erase_of_mem` —
  see `coordsTrimmed_length` in `ToricCodeNStabilizerCode.lean` for the pattern.

## Stabilizer-code packaging (trimmed generator lists)

`StabilizerCode n k` requires `generatorsList.length = n - k` via its
`generators_length` field, i.e. an **independent** generator list.
Concrete codes whose natural generator list has redundancies (toric,
color codes, etc.) need a *trimmed* list to populate it.

For the toric code, the natural `generatorsList L` in `ToricCodeN.lean`
has length `2L²` (all vertex + face stabs), but `StabilizerCode.generators_length`
needs `numQubits L - 2 = 2L² - 2`. The packaging is therefore built
separately in `ToricCodeNStabilizerCode.lean` with a trimmed list — see
the comment at `ToricCodeN.lean:613` for the cross-reference.

**Pattern for new packagings** (see `ToricCodeNStabilizerCode.lean`):

1. Define a trimmed list `generatorsListPackaged L` whose closure equals
   the existing `(stabilizerGroup L).toSubgroup`. Closure equality requires
   showing each *dropped* generator is in the closure of the kept ones —
   i.e. the homological identities.
2. Build the `StabilizerCode n k` directly with the trimmed list as
   `generatorsList`.
3. Expose `(toricStabilizerCode L).toStabilizerGroup.toSubgroup =
   (stabilizerGroup L).toSubgroup` as a public lemma; use it to translate
   stabilizer-group-based proofs to stabilizer-code-based proofs via
   `IsNontrivialLogicalOperator_of_toSubgroup_eq`.

This keeps existing distance proofs (which run against `stabilizerGroup L`)
intact instead of forcing a downstream rewrite.

## Umbrella files (orphan-module trap)

New modules under `Codes/`, `Lattice/`, etc. **must be imported in the
sibling umbrella file** (`QEC/Stabilizer/Codes.lean`, `Lattice.lean`,
…). Files not in any umbrella are unreachable from the default `lake
build` target — never compiled, never linted, errors silently hidden.
`QuantumHamming.lean` sat in this orphan state with two stale
`Nat.xor_*` references that `lake build` never surfaced. When adding
a module, also append the import.

## Cleanup recipes

One-time conversion patterns for linter sweeps and mathlib-version bumps
(nested `induction'` on `Fin L`, structure-builder `refine` chains hit
by `linter.style.multiGoal`, closure-induction case naming): see
`docs/lean-conversion-recipes.md`. Pull it in when you hit the
corresponding warning class.
