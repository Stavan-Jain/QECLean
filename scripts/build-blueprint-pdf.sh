#!/usr/bin/env bash
# Render the printable blueprint to blueprint/print/print.pdf.
#
# Why a script rather than `leanblueprint pdf`, which blueprint/README.md
# documents: that command drives the build through `latexmk`, which TeX Live's
# `basic` scheme does not ship, and it assumes `leanblueprint` itself is on
# PATH. This script needs neither -- only `lake` and `xelatex` -- and runs the
# same engine with the same flags latexmkrc specifies.
#
# It also handles the three things that are easy to get wrong by hand:
#
#   1. A Lean edit does not reach the PDF until `lake build
#      QECBlueprint:blueprint` re-emits the per-node LaTeX under
#      .lake/build/blueprint. content.tex's \inputleannode{} reads that
#      directory, not QECBlueprint.lean, so skipping the step rebuilds the PDF
#      with the previous prose and no warning.
#   2. \cref numbers come from print.aux, so one xelatex pass renders stale
#      cross-references. Passes are repeated here until the labels settle.
#   3. TEXINPUTS must name the current directory or kpsewhich cannot resolve
#      \input{macros/common}. See blueprint/README.md.
#
# Options:
#   --tex-only   Skip both lake builds. Use when only blueprint/src/*.tex
#                changed -- the emitted node files are already current.
#   --open       Open the finished PDF.
set -euo pipefail

tex_only=0
open_pdf=0
while [ $# -gt 0 ]; do
  case "$1" in
    --tex-only) tex_only=1 ;;
    --open) open_pdf=1 ;;
    -h|--help) awk 'NR>1 && !/^#/{exit} NR>1{sub(/^# ?/,""); print}' "$0"; exit 0 ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
  shift
done

root="$(cd "$(dirname "$0")/.." && pwd)"
src="$root/blueprint/src"
out="$root/blueprint/print"

# MacTeX installs here and does not always end up on a non-login shell's PATH.
command -v xelatex >/dev/null || PATH="/Library/TeX/texbin:$PATH"
command -v xelatex >/dev/null || {
  echo "xelatex not found. Install MacTeX (or any TeX Live with xelatex)," >&2
  echo "or add its bin directory to PATH." >&2
  exit 1
}

# A whole-repo build prints thousands of linter warnings, which would bury the
# one line that matters here. Keep the log and show it only if the build fails.
lake_log="$out/lake-build.log"

run_lake() {
  echo "==> lake build $1"
  lake build "$1" >"$lake_log" 2>&1 || {
    echo >&2
    echo "lake build $1 failed:" >&2
    grep -E '^(error|.*: error)' "$lake_log" | head -20 >&2
    echo >&2
    echo "Full output: $lake_log" >&2
    exit 1
  }
}

if [ "$tex_only" = 0 ]; then
  mkdir -p "$out"
  # Two targets, and the split matters. The first elaborates the attributes and
  # is the only thing in the repo that fails when an annotated declaration has
  # been renamed or removed; the second extracts the LaTeX.
  run_lake QECBlueprint
  run_lake QECBlueprint:blueprint
fi

nodes="$root/.lake/build/blueprint/module/QECBlueprint.artifacts"
[ -d "$nodes" ] || {
  echo "no extracted blueprint nodes at $nodes." >&2
  echo "Drop --tex-only so the lake builds run." >&2
  exit 1
}

mkdir -p "$out"
cd "$src"

# `xelatex -synctex=1` is what latexmkrc asks latexmk to run; -halt-on-error
# turns a TeX error into a nonzero exit instead of a PDF that is quietly
# missing a chapter.
run_pass() {
  TEXINPUTS=".:" xelatex -synctex=1 -interaction=nonstopmode -halt-on-error \
    -output-directory="$out" print.tex >/dev/null 2>&1 || {
    echo >&2
    echo "xelatex failed. From $out/print.log:" >&2
    grep -n -A5 '^!' "$out/print.log" | head -40 >&2
    echo >&2
    echo "Full transcript: $out/print.log" >&2
    exit 1
  }
}

# Four passes is a ceiling, not a target: a blueprint whose labels have not
# converged by then has a genuine cross-reference problem worth seeing.
max_passes=4
for pass in $(seq 1 $max_passes); do
  echo "==> xelatex (pass $pass)"
  run_pass
  grep -q 'Rerun to get\|Label(s) may have changed' "$out/print.log" || break
  [ "$pass" -lt "$max_passes" ] || {
    echo "warning: cross-references still unsettled after $max_passes passes." >&2
    echo "Check $out/print.log for an undefined or duplicated label." >&2
  }
done

# TeX wraps the transcript at ~79 columns, and an absolute -output-directory is
# long enough that "(19 pages)." routinely straddles the break. Join the lines
# before matching, and treat a miss as cosmetic rather than fatal.
pages=$(tr '\n' ' ' < "$out/print.log" | tr -s ' ' \
          | sed -n 's/.*Output written on [^ ]* (\([0-9]*\) pages\{0,1\}).*/\1/p' || true)
echo
echo "  $out/print.pdf${pages:+  ($pages pages)}"

# Undefined references survive the build, so say so rather than leaving a "??"
# in the PDF to be found by a reader.
if grep -q 'LaTeX Warning: Reference .* undefined' "$out/print.log"; then
  echo
  echo "warning: undefined references (these render as '??'):" >&2
  grep -o "LaTeX Warning: Reference \`[^']*'" "$out/print.log" | sort -u >&2
fi

# `[ ... ] && open` as the last statement would trip `set -e` whenever the test
# is false, failing a build that in fact succeeded.
if [ "$open_pdf" = 1 ]; then
  open "$out/print.pdf"
fi
