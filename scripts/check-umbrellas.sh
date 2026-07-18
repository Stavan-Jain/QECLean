#!/usr/bin/env bash
# Orphan-module check: every D/*.lean must be imported by its umbrella.
# Umbrella convention: sibling D.lean (Codes/Toric.lean for Codes/Toric/),
# with the top-level inside-umbrella exceptions (QEC/Foundations/Foundations.lean,
# QEC/Stabilizer/Stabilizer.lean, QEC/RepetitionCode/RepetitionCode.lean).
# Exit 1 if any orphan is found.
set -u
cd "$(dirname "$0")/.."
status=0
while IFS= read -r dir; do
  base="${dir%/}"
  umbrella="${base}.lean"
  inner="${base}/$(basename "$base").lean"
  [ -f "$umbrella" ] || { [ -f "$inner" ] && umbrella="$inner"; } || continue
  while IFS= read -r f; do
    [ "$f" = "$umbrella" ] && continue
    mod="$(echo "${f%.lean}" | tr '/' '.')"
    if ! grep -q "^import ${mod}$" "$umbrella"; then
      # transitive: a sub-umbrella may import it (one level down)
      sub="$(dirname "$f").lean"
      if [ -f "$sub" ] && grep -q "^import ${mod}$" "$sub"; then continue; fi
      echo "ORPHAN: $mod (not imported by $umbrella)"
      status=1
    fi
  done < <(find "$base" -maxdepth 1 -name '*.lean')
done < <(find QEC -type d)
exit $status
