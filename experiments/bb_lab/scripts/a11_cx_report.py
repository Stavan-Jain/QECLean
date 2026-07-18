"""A11 CX — generate data/a11/cx/REPORT.md from the hunt + probe streams."""

from __future__ import annotations

import collections
import json
import sys
from pathlib import Path

LAB_ROOT = Path(__file__).resolve().parent.parent
CX_DIR = LAB_ROOT / "data" / "a11" / "cx"


def load(path: Path) -> list[dict]:
    rows = []
    if path.exists():
        for line in path.open():
            try:
                rows.append(json.loads(line))
            except Exception:
                continue
    return rows


def main() -> None:
    hunt_rows: list[dict] = []
    for p in sorted(CX_DIR.glob("hunt_*.jsonl")):
        hunt_rows += load(p)
    nbr = load(CX_DIR / "neighbors.jsonl")
    exh = load(CX_DIR / "exhaustb.jsonl")
    slc = load(CX_DIR / "slice.jsonl")

    by = collections.defaultdict(collections.Counter)
    csafe = []
    cx = []
    for r in hunt_rows + nbr:
        key = (r.get("frame", "?"), f"{r.get('wA','?')}+{r.get('wB','?')}")
        st = r.get("stage", "?")
        by[key]["pairs"] += 1
        if st != "axes":
            by[key][st] += 1
            continue
        for a in r.get("axes", []):
            v = a.get("verdict", "?")
            by[key][v] += 1
            if a.get("csafe"):
                csafe.append((r, a))
            if v == "COUNTEREXAMPLE":
                cx.append((r, a))

    hdr = ["pairs", "k0", "dbase_over_cap", "d1", "k_drift", "no_tight_witness",
           "safe_floor_fail", "CSAFE_DOUBLES", "CSAFE_TRUE_unladdered",
           "COUNTEREXAMPLE"]
    lines = [
        "# A11 CX — counterexample hunt for `C-safe => literal-lift doubling`",
        "",
        f"Hunt rows: {len(hunt_rows)} sampled pairs + {len(nbr)} targeted "
        "neighborhood mutations.  A cell = (frame, A, B, axis); C-safe = "
        "k preserved + tight witness + safe floor (parity-safe SAT coset "
        "ladders, lo = d).  Verdict oracle: exact SAT `x_distance` at cap 2d.",
        "",
        "## Verdict",
        "",
        f"**Counterexamples found: {len(cx)}.**" if cx else
        "**No counterexample found.** Every C-safe-true cell that was "
        "laddered doubled exactly.",
        "",
        "## Coverage (per frame x weight pair; counts are axis-cells except "
        "`pairs`/`k0`/`dbase_over_cap`/`d1`)",
        "",
        "| frame | wA+wB | " + " | ".join(hdr) + " |",
        "|---|---|" + "---:|" * len(hdr),
    ]
    tot = collections.Counter()
    for key in sorted(by):
        c = by[key]
        tot.update(c)
        lines.append(f"| {key[0]} | {key[1]} | " +
                     " | ".join(str(c.get(h, 0)) for h in hdr) + " |")
    lines.append("| **total** | | " +
                 " | ".join(f"**{tot.get(h, 0)}**" for h in hdr) + " |")

    n_csafe_cells = len({(r["frame"], r["A"], r["B"], a["axis"]) for r, a in csafe})
    lines += ["", f"C-safe-true cells: {n_csafe_cells} (unique), all with "
              "d(cover) = 2 d(base) where laddered.", ""]

    # near-miss tables
    lines += ["## Near-miss: dangerous-rung slice margins on C-safe cells", ""]
    lines += [f"- `slice.jsonl` (subset-census probe): {len(slc)} cells, "
              f"{sum(1 for r in slc if isinstance(r.get('rung_dips'), int) and r['rung_dips'] > 0)} dips.",
              f"- `exhaustb.jsonl` (exhaustive light-b census): {len(exh)} cells, "
              f"{sum(1 for r in exh if isinstance(r.get('rung_dips'), int) and r['rung_dips'] > 0)} dips.", ""]
    margins = []
    for r in exh:
        if isinstance(r.get("min_margin"), int):
            margins.append((r["min_margin"], r))
    margins.sort(key=lambda t: t[0])
    if margins:
        lines += ["Sharpest relaxed-slice margins (slice_min - 2d; relaxed rho "
                  "pool => lower bound on the true rung slack):", "",
                  "| margin | frame | axis | d | A | B | n light b | hunt verdict |",
                  "|---:|---|---|---:|---|---|---:|---|"]
        for mg, r in margins[:12]:
            lines.append(f"| {mg} | {r['frame']} | {r['axis']} | {r['d']} "
                         f"| `{r['A']}` | `{r['B']}` | {r.get('n_light_b_total','?')} "
                         f"| {r.get('hunt_verdict','?')} |")
    zero = sum(1 for mg, _ in margins if mg == 0)
    neg = sum(1 for mg, _ in margins if mg < 0)
    lines += ["", f"Margin histogram over cells with measurable light-b rungs: "
              f"{collections.Counter(mg for mg, _ in margins).most_common()} "
              f"({zero} tight cells, {neg} dips).", ""]
    with_b = sum(1 for r in exh if r.get("n_light_b_total", 0) > 0)
    lines += [f"Cells with a nonempty light-stabilizer census (exhaustive): "
              f"{with_b}/{len(exh)}.", ""]
    if cx:
        lines += ["## COUNTEREXAMPLES", ""]
        for r, a in cx:
            lines.append(f"- {r['frame']} axis {a['axis']} A=`{r['A']}` "
                         f"B=`{r['B']}` d {r['d_base']} -> {a['d_cover']}")
    out = CX_DIR / "REPORT.md"
    out.write_text("\n".join(lines) + "\n")
    print(f"wrote {out} ({len(lines)} lines)")


if __name__ == "__main__":
    main()
