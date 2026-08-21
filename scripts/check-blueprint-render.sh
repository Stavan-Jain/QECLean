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

exit $fail
