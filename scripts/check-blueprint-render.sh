#!/usr/bin/env bash
# Verify that the *rendered* blueprint actually contains its nodes.
#
# Why this exists: `lake build QECBlueprint:blueprint` can emit all 85 node
# files correctly and `leanblueprint web` can still exit 0 having loaded none
# of them, producing a site with the full narrative and an empty dependency
# graph. That is exactly what happened on the first run of this workflow.
#
# The cause is plasTeX's `\input` resolution. plasTeX shells out to `kpsewhich`
# (a TeX Live binary); when it is absent, plasTeX 3.1 falls back to a
# pure-Python search that matches only a bare filename against the entries of a
# single directory:
#
#     for path in [x for x in paths if x]:
#         if name in os.listdir(path):
#
# Every `\input` argument carrying a path separator therefore fails to resolve:
# `macros/common`, the `../../.lake/...` index, and the absolute paths
# LeanArchitect writes inside its own generated files. plasTeX logs a warning
# and carries on, so the failure is silent.
#
# Checking the extraction side alone does not catch this -- the producer is
# fine, the consumer never reads it. So verify the consumer's output directly.
set -u

web=blueprint/web
content=blueprint/src/content.tex
fail=0

[ -d "$web" ] || { echo "::error::$web does not exist -- run 'leanblueprint web' first"; exit 1; }

missing=0
total=0
while read -r label; do
  [ -n "$label" ] || continue
  total=$((total + 1))
  if ! grep -rqF "$label" "$web"/*.html; then
    echo "::error::node '$label' is included by content.tex but absent from the rendered output"
    missing=$((missing + 1))
    fail=1
  fi
done < <(grep -oP '\\inputleannode\{\K[^}]+' "$content" | sort -u)

echo "rendered-node check: $total labels included, $missing missing"

graph="$web/dep_graph_document.html"
if [ ! -s "$graph" ]; then
  echo "::error::dependency graph was not generated ($graph)"
  exit 1
fi

# plastexdepgraph embeds a graphviz `digraph`; count its node declarations.
gnodes=$(grep -oP '"\K[^"]+(?="\s*\[)' "$graph" | sort -u | wc -l)
echo "dependency graph declares $gnodes nodes"
if [ "$gnodes" -lt 1 ]; then
  echo "::error::dependency graph is empty -- plasTeX rendered no blueprint nodes"
  fail=1
fi

# --- the focused-subgraph control ------------------------------------------
#
# `blueprint/src/dep_graph_focus.js` restricts the graph to one node's
# transitive dependencies. It has two dependencies on machinery we do not own,
# and both fail quietly rather than loudly, so assert them here.
#
# 1. plasTeX has to copy the file out of blueprint/src and the dep-graph
#    template has to emit a <script> tag for it. A typo in the `extra-js` line
#    of plastex.cfg logs one line to stderr and renders a page without it.
# 2. The script recovers the graphviz source by reading it back out of the
#    template's inline `.renderDot(`...`)` call, because the template
#    interpolates the dot straight into that call rather than into a variable.
#    If plastexdepgraph ever changes that shape the script degrades to leaving
#    the stock graph alone -- correct, but silent. Catch it at build time.

focus_js="$web/js/dep_graph_focus.js"
if [ ! -s "$focus_js" ]; then
  echo "::error::$focus_js missing -- check the extra-js line in blueprint/src/plastex.cfg"
  fail=1
elif ! grep -qF 'js/dep_graph_focus.js' "$graph"; then
  echo "::error::$graph does not load dep_graph_focus.js"
  fail=1
elif ! grep -qF 'renderDot(`' "$graph"; then
  echo "::error::the dependency-graph template no longer renders via renderDot(\`...\`);"
  echo "::error::dep_graph_focus.js reads the graph source from that call and will now no-op"
  fail=1
else
  echo "focused-subgraph control: script present and graph source readable"
fi

exit $fail
