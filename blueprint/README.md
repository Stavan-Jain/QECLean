# The QECLean blueprint

A [leanblueprint](https://github.com/PatrickMassot/leanblueprint) blueprint for
this library, with the node content generated from Lean by
[LeanArchitect](https://github.com/hanwenzhu/LeanArchitect)
([arXiv:2601.22554](https://arxiv.org/abs/2601.22554)).

## What is generated and what is written by hand

| | Where | Edited by |
|---|---|---|
| Node statements, proof sketches, titles, `\lean{}`, `\leanok`, `\uses{}` | `QECBlueprint.lean` | you, as `@[blueprint]` options |
| Narrative, chapters, ordering | `blueprint/src/content.tex` | you |
| LaTeX preamble, macros, plasTeX config | `blueprint/src/` | you, rarely |
| `.lake/build/blueprint/**` | generated | **never** — regenerate instead |

The important consequence: **there is no second copy of the mathematics.** A
blueprint node is not a LaTeX transcription of a Lean theorem that can drift out
of date; it is the Lean theorem, with prose attached. Renaming a declaration
breaks the build rather than silently orphaning a node, and the `\uses{}` edges
are read off the actual proof terms rather than maintained by hand.

`\leanok` is likewise derived, not asserted: LeanArchitect marks a node green
exactly when its constant is free of `sorryAx`. Since this library is sorry-free
by policy, every node is green — the graph is a map of the architecture rather
than a progress tracker.

## Building it

Prerequisites: the usual Lean toolchain, plus

```bash
sudo apt-get install graphviz libgraphviz-dev   # for the dependency graph
pip install leanblueprint
```

Then, from the repository root:

```bash
lake build QECBlueprint             # elaborate the annotations
lake build QECBlueprint:blueprint   # extract the LaTeX
leanblueprint web                   # render to blueprint/web/
leanblueprint pdf                   # render to blueprint/print/ (needs xelatex)
```

Open `blueprint/web/index.html`. The dependency graph is linked from the
navigation bar.

`lake build QECBlueprint` is the step that matters day to day: it is what fails
when a declaration named in an annotation has been renamed or removed. The
extraction step is cheap once the build is warm, but note that it loads the
whole `QEC` environment into a single process, so it wants the same headroom as
building the bivariate-bicycle leaves.

## Inspecting a single node

```lean
#show_blueprint Quantum.StabilizerGroup.ToricCodeN.toricCodeN_distance_eq_L
```

prints the exact LaTeX that will be emitted for that node, including the
inferred `\uses{}` list — useful when an edge you expected in the graph is
missing, which usually means an intermediate declaration is also tagged and is
absorbing the edge.

There is also a machine-readable form:

```bash
lake build QECBlueprint:blueprintJson   # .lake/build/blueprint/**/*.json
```

## Adding a node

1. Pick the declaration. Prefer the statement a reader would want to see over
   the lemma that happens to be convenient in Lean.
2. Add an `attribute [blueprint "label" ...] Fully.Qualified.Name` block to the
   appropriate chapter of `QECBlueprint.lean`. Use a doc comment
   (`/-- ... -/`) rather than a string literal for anything containing LaTeX —
   a Lean string would read `\mathcal` as an escape sequence and fail to parse.
3. Add a matching `\inputleannode{label}` in `blueprint/src/content.tex`. A node
   that is never included simply does not appear; CI checks the reverse
   direction (an inclusion with no node fails the build).
4. Rebuild.

Remember that tagging a declaration also changes the graph *around* it:
dependency inference stops at the nearest tagged ancestor, so a new node in the
middle of a chain will take over edges that previously ran past it.

## Deployment

The `Blueprint` workflow builds on every push and uploads `blueprint/web` as a
run artifact. Publishing to GitHub Pages is a manual `workflow_dispatch` with
the `deploy` input set, because this repository's Pages site currently serves
the path-preserving dashboard redirect from `pages-redirect.yml`, and whichever
workflow deploys last wins. The deploy path keeps that redirect as `404.html`,
so old `/QECLean/<path>` links still bounce to the qec-lab dashboard; only the
site root changes meaning. If you want the blueprint published automatically,
move the deploy steps onto the `push` trigger and retire `pages-redirect.yml`.

`\dochome` in `web.tex` points at `https://stavan-jain.github.io/QECLean/docs`,
so the `\lean{}` links resolve once API documentation is deployed there
(`lean_action_ci.yml` builds it on tags and manual dispatch).

## Notes

- Node files are named after their LaTeX label, so a label containing a colon
  (`def:pauli-weight` → `def:pauli-weight.tex`) produces a filename that Windows
  cannot represent. Colons are the leanblueprint convention and work on Linux
  and macOS; on Windows, build the blueprint under WSL.
- The `\input` paths inside the generated index are absolute, so the extracted
  LaTeX is not portable between checkouts. That is fine — it is regenerated by
  `lake build QECBlueprint:blueprint` and never committed.
