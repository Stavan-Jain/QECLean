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
sudo apt-get install graphviz libgraphviz-dev texlive-binaries
pip install leanblueprint
```

On macOS none of that apt line applies: `kpsewhich` comes with MacTeX (already
on `PATH` as `/Library/TeX/texbin/kpsewhich`), and current `pygraphviz` wheels
bundle graphviz, so `pip install leanblueprint` into a virtualenv is the whole
setup — no Homebrew graphviz needed.

`texlive-binaries` is **not optional**, even though nothing here compiles TeX
for the web build: it provides `kpsewhich`, which plasTeX shells out to in order
to resolve `\input` paths. See "If the blueprint renders with no nodes" below —
this is the one setup mistake that fails silently.

Then, from the repository root:

```bash
lake build QECBlueprint             # elaborate the annotations
lake build QECBlueprint:blueprint   # extract the LaTeX
TEXINPUTS=".:" leanblueprint web    # render to blueprint/web/
TEXINPUTS=".:" leanblueprint pdf    # render to blueprint/print/ (needs xelatex)

bash scripts/check-blueprint-render.sh   # assert the nodes actually rendered
```

`TEXINPUTS` is needed because `texlive-binaries` installs no texmf tree, so
`kpsewhich` has no default search path of its own. A full TeX Live installation
sets one up and you can drop the prefix.

Then serve it, rather than opening the files directly:

```bash
bash scripts/preview-blueprint.sh
```

It serves on port 8000, stepping up to the next free port if something else
already has it (`--port N` to choose). Localhost only.

The dependency graph is linked from the navigation bar. It has to be served
over HTTP or the graph comes up empty — see the next section for why.

### Working on the graph without building Lean

The dependency-graph page's behaviour lives in `blueprint/src/` as ordinary CSS
and JavaScript (`extra_styles.css`, `dep_graph_focus.js`), and none of it needs
the Lean half to be rebuilt. To iterate on it, take the last CI render instead:

```bash
bash scripts/preview-blueprint.sh --from-ci
```

That downloads the newest successful Blueprint run's `blueprint-web` artifact
with `gh`, copies in the current `extra-css` / `extra-js` files the way plasTeX
would, and serves the result — no Lean build, no `leanblueprint`, no graphviz.
Re-run it after each edit. Because it is the page CI actually emitted, it
catches the things a hand-written test page would not.

The repository is passed to `gh` explicitly, derived from the `origin` remote:
this checkout has two GitHub remotes (`origin` and `lab`), so `gh` cannot infer
which one a run belongs to and would otherwise demand a `gh repo set-default`.
Set `BLUEPRINT_GH_REPO=owner/name` to read runs from somewhere else, such as
upstream while working on a fork.

### If the dependency graph page is blank

Symptom: the chapters and their theorem/definition boxes all render correctly,
but `dep_graph_document.html` shows only the "Dependencies" header and an empty
"Legend" — no graph.

Cause: you opened the file directly, over `file://`. The graph is not baked into
the HTML as static SVG; it is drawn in the browser by `d3-graphviz.js` and
`hpcc.min.js`, which load `graphvizlib.wasm` at runtime. Chrome refuses those
loads from a `file://` origin (`Unsafe attempt to load URL ... from frame with
URL file://...`), so the renderer never runs and the container stays empty.

This is not a build problem — the assets are all present under `blueprint/web/js/`
and the graph data is embedded in the page as a graphviz `digraph`.

Fix: serve the directory over HTTP, which is all
`scripts/preview-blueprint.sh` does.

```bash
bash scripts/preview-blueprint.sh
# then open http://localhost:8000/dep_graph_document.html
```

Measured in headless Chromium on the same directory: over `file://` the page
renders 0 graph nodes and 0 edges; over `http://` it renders all 85 nodes and
their edges. The deployed GitHub Pages copy is served over HTTPS, so it does
not need this workaround.

### If the blueprint renders with no nodes

Symptom: every chapter of narrative is present, each one ends abruptly where a
definition or theorem should be, and the dependency graph page is blank.

Cause: plasTeX could not resolve the `\input`s that pull in the extracted
nodes. It reports this as a warning and still exits 0:

```
WARNING: File not found: macros/common
WARNING: File not found: ../../.lake/build/blueprint/library/QECBlueprint
WARNING: unrecognized command/environment: inputleannode
```

plasTeX shells out to `kpsewhich` for path resolution. When that binary is
missing it falls back to a pure-Python search that matches only a bare filename
against the entries of a single directory (`if name in os.listdir(path)`), so
every `\input` argument containing a path separator fails: `macros/common`, the
`../../` index, and — decisively — the *absolute* paths LeanArchitect writes
inside its own generated files. That last one is why flattening our own paths
would not have been a fix; `kpsewhich` has to be present.

Fix: install `texlive-binaries` and set `TEXINPUTS` as above. `scripts/check-blueprint-render.sh`
catches the condition, and CI runs it on every push.

`lake build QECBlueprint` is the step that matters day to day: it is what fails
when a declaration named in an annotation has been renamed or removed. The
extraction step is cheap once the build is warm, but note that it loads the
whole `QEC` environment into a single process, so it wants the same headroom as
building the bivariate-bicycle leaves.

## Reading one result's dependencies

The dependency graph shows all 85 nodes at once, which answers "what is in this
library" but not "what does this one theorem actually rest on". The controls
above the graph narrow it to a single node's transitive dependencies:

- **Focus on** — a node, by full label (`def:steane7`), by the short name shown
  on the graph (`steane7`), or by any unambiguous fragment of either. The list
  is a `<datalist>`, so typing filters it.
- **show** — `what it depends on` (the default) walks *up* to everything the
  node rests on; `what depends on it` walks down to everything built on top of
  it; `both directions` is the union.
- **to depth** — how many edges out to walk. `all the way` is the full
  transitive closure; a small number is useful on a node near the top of the
  library, where the closure is most of the graph.
- **Show everything** restores the full graph.

The subgraph is laid out afresh rather than highlighted in place, so what you
get is a small readable picture instead of a scattering of nodes across the
original canvas. The focused node is drawn with a heavy double outline; the
node colours are left alone, because the legend gives them a meaning.

Clicking a node opens its statement, as before, and that panel now carries a
**Focus on this** button.

A focused view is a URL, so it can be linked from a discussion or an issue:

```
dep_graph_document.html?focus=thm:gross-distance&dir=up
dep_graph_document.html?focus=def:steane7&dir=up&depth=2
```

`dir` is `up`, `down`, or `both`; `depth` is omitted for the full closure.

**On edge direction**, which is easy to get backwards: plastexdepgraph draws
`A -> B` to mean *B uses A*, so arrows run from a prerequisite towards the
result that needs it. The dependencies of a node are therefore its ancestors,
found by walking the arrows backwards — which is what `what it depends on`
does.

### How it is wired in

[`src/dep_graph_focus.js`](src/dep_graph_focus.js), listed as `extra-js` in
`plastex.cfg`. plasTeX copies any `extra-js` file from `blueprint/src/` into
`web/js/` and the upstream dependency-graph template emits a `<script>` tag for
it, so no template is forked. It is loaded on every page and does nothing on
the ones with no graph.

The one thing it needs and is not handed is the graphviz source: the template
interpolates it directly into a ``.renderDot(`...`)`` call rather than into a
variable, so the script reads it back out of that call, parses it, and re-emits
the induced subgraph. If that ever stops working the script leaves the stock
graph untouched rather than breaking the page — silent, so
`scripts/check-blueprint-render.sh` asserts the shape it depends on and CI
fails instead.

Two smaller things worth knowing before editing it:

- Register `end` handlers *before* calling `renderDot`, never chained after it.
  Once the graphviz wasm is loaded a render completes synchronously and
  dispatches `end` before `renderDot` returns, so a handler attached afterwards
  never fires. Upstream can chain because its render is the one that waits for
  the wasm to load.
- Re-renders rebind only the node click handlers, not upstream's whole
  `interactive()`. That function also binds the legend toggle and the modal
  close buttons with jQuery, whose handlers accumulate — calling it twice makes
  the legend toggle a no-op.

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
