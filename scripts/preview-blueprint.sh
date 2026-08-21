#!/usr/bin/env bash
# Serve the rendered blueprint over HTTP.
#
# Why a script rather than `open blueprint/web/index.html`: the dependency
# graph is not baked into the page as static SVG. It is drawn in the browser by
# d3-graphviz, which loads `graphvizlib.wasm` at runtime, and Chrome refuses
# that load from a `file://` origin -- so opening the file directly gives you
# the full narrative and a blank graph. See blueprint/README.md.
#
# Two sources for the site:
#
#   (default)   blueprint/web, as produced by `leanblueprint web`.
#
#   --from-ci   The newest successful Blueprint run's artifact, downloaded with
#               `gh`, with blueprint/src's `extra-css` / `extra-js` files copied
#               in the way plasTeX would. This is the fast path for working on
#               the front-end assets (dep_graph_focus.js, extra_styles.css):
#               it needs no Lean build, no leanblueprint and no graphviz, and
#               it exercises the real emitted page rather than a mock-up.
#               Re-run it after every edit to those files.
set -euo pipefail

port=8000
from_ci=0
while [ $# -gt 0 ]; do
  case "$1" in
    --from-ci) from_ci=1 ;;
    --port) port="${2:?--port needs a number}"; shift ;;
    -h|--help) sed -n '2,20p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
  shift
done

root="$(cd "$(dirname "$0")/.." && pwd)"
web="$root/blueprint/web"
src="$root/blueprint/src"

if [ "$from_ci" = 1 ]; then
  command -v gh >/dev/null || { echo "gh is required for --from-ci" >&2; exit 1; }

  # Name the repository explicitly. This checkout has two GitHub remotes --
  # `origin` (the library) and `lab` (the research repo it was split out of) --
  # so `gh` cannot infer which one a run belongs to and asks for
  # `gh repo set-default`. Deriving it from `origin` keeps that out of the
  # user's global gh config. $BLUEPRINT_GH_REPO overrides, e.g. to read runs
  # from upstream while working on a fork.
  repo="${BLUEPRINT_GH_REPO:-}"
  if [ -z "$repo" ]; then
    origin=$(git -C "$root" remote get-url origin 2>/dev/null || true)
    origin="${origin%.git}"
    case "$origin" in
      *github.com[:/]*) repo=$(printf '%s' "${origin#*github.com}" | sed 's#^[:/]##') ;;
    esac
  fi
  [ -n "$repo" ] || {
    echo "could not work out the GitHub repository from the 'origin' remote." >&2
    echo "Set it explicitly:  BLUEPRINT_GH_REPO=owner/name $0 --from-ci" >&2
    exit 1
  }

  run=$(gh run list --repo "$repo" --workflow=blueprint.yml --status=success \
          --limit 1 --json databaseId --jq '.[0].databaseId // empty')
  [ -n "$run" ] || { echo "no successful Blueprint run in $repo to download from" >&2; exit 1; }
  echo "downloading blueprint-web from $repo run $run"
  rm -rf "$web"
  mkdir -p "$web"
  gh run download "$run" --repo "$repo" -n blueprint-web -D "$web"

  # plasTeX copies each extra-css/extra-js file out of blueprint/src and adds a
  # tag for it to every page it renders. Redo that here, so assets newer than
  # the downloaded artifact -- or edited since -- are the ones being served.
  while IFS= read -r line; do
    kind="${line%%=*}"; file="${line#*=}"
    case "$kind" in
      extra-css) dir=styles; tag="<link rel=\"stylesheet\" href=\"styles/$file\" />" ;;
      extra-js)  dir=js;     tag="<script type=\"text/javascript\" src=\"js/$file\"></script>" ;;
      *) continue ;;
    esac
    [ -f "$src/$file" ] || { echo "warning: $src/$file does not exist" >&2; continue; }
    mkdir -p "$web/$dir"
    cp "$src/$file" "$web/$dir/"
    for page in "$web"/*.html; do
      grep -qF "$dir/$file" "$page" && continue
      # Both tags belong at the end of the document: the stylesheet must win
      # over the theme, and the script must run after the inline setup script
      # that kicks off the initial render.
      python3 - "$page" "$tag" <<'PY'
import sys, pathlib
page, tag = pathlib.Path(sys.argv[1]), sys.argv[2]
s = page.read_text()
page.write_text(s.replace('</body>', tag + '\n</body>', 1) if '</body>' in s else s + tag)
PY
    done
    echo "  applied $file"
  done < <(grep -E '^extra-(css|js)=' "$src/plastex.cfg" || true)
fi

[ -d "$web" ] || {
  echo "$web does not exist. Build it first:" >&2
  echo "    lake build QECBlueprint:blueprint && TEXINPUTS=\".:\" leanblueprint web" >&2
  echo "  or fetch the last CI render:  bash scripts/preview-blueprint.sh --from-ci" >&2
  exit 1
}

echo
echo "  http://localhost:$port/index.html"
echo "  http://localhost:$port/dep_graph_document.html"
echo "  http://localhost:$port/dep_graph_document.html?focus=def:steane7&dir=up"
echo
echo "Ctrl-C to stop."
cd "$web"
exec python3 -m http.server "$port"
