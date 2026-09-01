# QECWidgets — infoview widgets (read me before editing)

ProofWidgets-based visualizations for working with the library in an editor.
Everything here is **untrusted display-layer meta code**: the widgets show
what weak-head reduction finds, proofs are still checked by the kernel as
usual, and nothing in `QEC/` imports this library. `QECWidgets` is a separate
`lean_lib` (same policy as `QECBlueprint`) so that only it depends on
ProofWidgets — which is already in the dependency tree via mathlib, so there
is no new `require` and no manifest change.

## The widgets

| Widget | Command | Recognizes | Shows |
|---|---|---|---|
| Pauli strip | `#pauli_strip e` | `NQubitPauliGroupElement n`, `NQubitPauliOperator n` (literal `n`) | colored per-qubit strip, phase, weight |
| Commutation views | `#pauli_strip e` | `Anticommute p q`, equalities between Pauli terms | both operands aligned, anticommuting/differing qubits ringed, parity verdict (`commutes_iff_even_anticommutes` as a picture) |
| Goal suggestion | `pauli_strip?` (tactic) | goals of the two proposition shapes | the goal's strip view; a "replace with decide" link when the verdict says it holds |
| Toric lattice | `#toric_chain e` | `C1 L` terms, `toric{X,Z}OperatorOfChain L c` (literal `L`) | the chain on the `L × L` torus; wrap edges as dashed stubs; X coral / Z blue |
| Check matrix | `#check_matrix e` | `List (NQubitPauliGroupElement n)` | `(X ∣ Z)` symplectic heatmap in the `checkMatrix` column convention, plus the Gram matrix (red = anticommuting pair) |

Four surfaces:

1. **Commands** (above) — put the cursor on the line, the widget renders in
   the infoview. Each command also logs a plain-text summary, so terminal
   users (and `lake build` logs) see something too.
2. **The `pauli_strip?` suggestion tactic** — inside a proof of a recognized
   proposition, renders the goal's strip view; when the parity verdict says
   the goal holds, the panel offers a link that replaces the tactic call
   with `decide` (the `rw??` pattern: a `mk_rpc_widget%` panel plus
   `MakeEditLink`).
3. **Expression presenters** — during a proof, add
   `with_panel_widgets [ProofWidgets.SelectionPanel] <tactics>` and
   shift-click any recognized expression in the goal; or use
   `ProofWidgets.GoalTypePanel` on a goal that *is* a recognized proposition.
4. **Text** — the logged summaries make the widgets usable (and testable)
   without an editor: `lean_diagnostic_messages` / build logs carry them.

Card headers are live terms (`exprName`, ProofWidgets' `InteractiveCode`):
hover for types and docs, click to jump to the definition.

The cards are deliberately minimal: a state bar (verdict green/red/amber, or
the operator's identity color), a dim header (expression + weight), the
diagram, and a compact verdict. Explanations live in hover tooltips and in
the logged text summaries — when adding to a widget, put detail there, not on
the card. Phases render as a leading glyph on the strip (`−`, `i`, `−i`;
nothing for `+1`), and row index labels appear only on strips that wrap.

All look and feel lives in `Style.lean`: the palette (`Accent` values) and
the `qecw-*` class stylesheet that every card embeds. Styling is class-based
on purpose — classes give hover states and transitions (inline styles
cannot), per-theme tuning (`vscode-dark` / `vscode-light` /
`vscode-high-contrast` body classes), and small RPC payloads (one class name
per cell instead of a repeated style object). When adding a widget, use the
existing classes and tokens; do not hand-roll inline colors. In SVG, never
put `var(...)` in a presentation attribute (it silently fails to parse) —
use a `qecw-svg-*` class or an inline `style` attribute instead.

`QECWidgets/Demo.lean` is the living gallery; it is imported by the umbrella,
so the demos compile in CI and cannot silently rot.

## How evaluation works

`Mul` on `NQubitPauliGroupElement` is `noncomputable`, so `#eval`-style
compilation is unavailable — but the terms still *reduce*, which is the same
fact that lets `decide` close `Anticommute` goals through the kernel.
`PauliEval.whnfCandidates` therefore normalizes in an escalating ladder:
`whnf` at default transparency, then `.all`, then `Kernel.whnf` (which
ignores `@[irreducible]`, i.e. sees exactly what `decide` sees). Concrete
generators, products of them, and `toricZOperatorOfChain`-style wrappers all
reduce; variables and hypotheses render as `?` cells with an "unresolved"
chip instead of failing.

Size caps (each cell costs a reduction): strips ≤ 512 qubits
(`maxStripQubits`), lattices `L ≤ 16` (`maxToricL`), check matrices ≤ 64
generators (`maxCheckRows`).

## Adding a widget — repo-specific rules learned the hard way

- **Copyright headers are required here.** Files *directly imported by a
  root-level module* (`QECWidgets.lean`) are exactly the ones
  mathlib's `linter.style.header` checks, so every content file needs the
  standard mathlib copyright block. (Files under `QEC/` dodge this only
  because the root imports them through umbrella files.)
- **Every `#`-command must log a message.** `linter.hashCommand` flags
  `#`-commands that emit nothing; the text summaries exist partly for this.
  Do not suppress the linter — emit useful text instead.
- **`decide`-style instances stay `local instance` in Demo.lean.** The
  group-element-level `DecidableEq` / `Decidable Anticommute` instances are
  deliberately not global — see the note in `PauliGroup/Commutation.lean`
  and CLAUDE.md § "Global vs. local instance discipline".
- Reuse `PauliEval` (reduction, `Fin`/`Nat`/ctor extraction) and the
  `PauliStrip` rendering helpers (`el`, `styled`, `chip`, `card`, colors)
  rather than duplicating them.
- New modules must be imported by `QECWidgets.lean` (the umbrella) — it is
  the build target CI runs (`lake build QECWidgets` in
  `lean_action_ci.yml`), and the lib stays outside `defaultTargets`.
