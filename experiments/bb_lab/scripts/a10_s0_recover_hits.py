"""A10 S0 — regenerate the A9 T2 presentation-anchorable hits and pin hit2/hit5.

The A9 run's `data/a9/t2_presentation_hits.json` and
`data/a9/t2_cover_ladders.json` were never committed; this script
reproduces both from the corpus duckdb, so the A10 descent screen has
its decisive bases (hit2/hit5) pinned with harness-independent literal
baselines.

Expected reproduction (A9 notes §T2): 812 Z6xZ6 k>0 corpus codes, 326
with d_exact >= 6, exactly 6 presentation-anchorable, canonical dedup =
gross-base class + 5 new; hit3/4/6 identified by their published
polynomials; hit2 x/y literal covers stay at d = 6; hit5-x reaches 8.

Subcommands:
    uv run python scripts/a10_s0_recover_hits.py hits      # fast-ish (~minutes)
    uv run python scripts/a10_s0_recover_hits.py ladders   # SAT, the 2 unknown hits x/y
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

LAB_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LAB_ROOT / "src"))
sys.path.insert(0, str(LAB_ROOT / "scripts"))

from bb_lab.canonical import canonical_pair, build_perm_table
from bb_lab.automorphism import automorphisms as bb_automorphisms
from bb_lab.checks import bb_check_matrices
from bb_lab.group import AbelianGroup
from bb_lab.poly import Poly
from bb_lab.sat_distance import x_distance

from a5_cover_cascade import presentation_anchorable
from a9_lean_target_screen import cover_group, lift_poly

HITS_JSON = LAB_ROOT / "data" / "a9" / "t2_presentation_hits.json"
LADDERS_JSON = LAB_ROOT / "data" / "a9" / "t2_cover_ladders.json"

# Published identities (A9 notes §T2 + addendum), used to label the dedup
# classes.  All five new hits share A = y^3+x+x^2 up to normalization.
KNOWN = {
    "gross_base": ("x^3 + y + y^2", "y^3 + x + x^2"),
    "hit3": ("y^3 + x + x^2", "y + x*y^2 + x^2"),
    "hit4": ("y^3 + x + x^2", "y^2 + x*y^3 + x^2*y"),
    "hit6": ("y^3 + x + x^2", "x*y + x^2*y^2 + x^3"),
}


def _canon_key(A_str: str, B_str: str, G: AbelianGroup, perms) -> tuple:
    A = Poly.from_string(A_str, G)
    B = Poly.from_string(B_str, G)
    return canonical_pair(A.support, B.support, G, perms=perms).key


def recover_hits() -> None:
    import duckdb

    con = duckdb.connect(str(LAB_ROOT / "data" / "bb_instances.duckdb"), read_only=True)
    rows = con.execute(
        "SELECT instance_id, A_poly, B_poly, k, d_exact FROM bb_instances "
        "WHERE group_struct = 'Z6xZ6' AND k > 0 AND d_exact >= 6 "
        "ORDER BY instance_id"
    ).fetchall()
    con.close()
    print(f"corpus: {len(rows)} Z6xZ6 k>0 d>=6 codes (A9 expects 326)")

    G = AbelianGroup((6, 6))
    hits = []
    t0 = time.time()
    for i, (iid, A_str, B_str, k, d) in enumerate(rows):
        ok, rep = presentation_anchorable(
            6, 6, Poly.from_string(A_str, G), Poly.from_string(B_str, G)
        )
        if ok:
            hits.append(
                {
                    "instance_id": iid,
                    "A": A_str,
                    "B": B_str,
                    "k": k,
                    "d": d,
                    "witness_A": sorted(rep.A.support),
                    "witness_B": sorted(rep.B.support),
                }
            )
            print(f"  ANCHORABLE {iid}  A=`{A_str}`  B=`{B_str}`  k={k} d={d}")
        if (i + 1) % 25 == 0:
            print(f"  ... {i+1}/{len(rows)}  ({time.time()-t0:.0f}s)", flush=True)
    print(f"presentation-anchorable: {len(hits)} (A9 expects 6)")

    # Dedup + label against the published identities.
    auts = bb_automorphisms(G)
    perms = build_perm_table(G, auts=auts)
    known_keys = {
        name: _canon_key(a, b, G, perms) for name, (a, b) in KNOWN.items()
    }
    for h in hits:
        key = _canon_key(h["A"], h["B"], G, perms)
        h["canonical_key"] = repr(key)
        h["label"] = next(
            (name for name, kk in known_keys.items() if kk == key), None
        )
    n_classes = len({h["canonical_key"] for h in hits})
    print(f"canonical classes among hits: {n_classes} (A9 expects 6)")

    unknown = [h for h in hits if h["label"] is None]
    print(f"unlabeled classes (candidates for hit2/hit5): {len(unknown)}")
    for h in unknown:
        print(f"  CANDIDATE {h['instance_id']}  A=`{h['A']}`  B=`{h['B']}`")

    HITS_JSON.parent.mkdir(parents=True, exist_ok=True)
    HITS_JSON.write_text(json.dumps(hits, indent=2))
    print(f"wrote {HITS_JSON}")


def run_ladders() -> None:
    """x/y literal-lift cover ladders for the unlabeled hits (n = 144).

    Non-doubling verdicts are cheap (SAT at the true cover distance
    after a short UNSAT ramp); a doubling verdict would contradict A9.
    """
    hits = json.loads(HITS_JSON.read_text())
    targets = [h for h in hits if h["label"] is None]
    G = AbelianGroup((6, 6))
    out = []
    for h in targets:
        A = Poly.from_string(h["A"], G)
        B = Poly.from_string(h["B"], G)
        row = {"instance_id": h["instance_id"], "A": h["A"], "B": h["B"]}
        for axis in ("x", "y"):
            Gc = cover_group(6, 6, axis)
            Ac, Bc = lift_poly(A, Gc), lift_poly(B, Gc)
            checks = bb_check_matrices(Ac, Bc)
            t0 = time.time()
            res = x_distance(checks, weight_upper_bound=13, verbose=True)
            row[f"{axis}_cover_d"] = res.distance
            print(
                f"{h['instance_id']} {axis}-cover: d = {res.distance} "
                f"({time.time()-t0:.1f}s)",
                flush=True,
            )
        out.append(row)
    LADDERS_JSON.write_text(json.dumps(out, indent=2))
    print(f"wrote {LADDERS_JSON}")
    print("A9 expects one base with x=y=6 (hit2) and one with x=8 (hit5).")

    # Empirical labeling: the A9 addendum pins hit5 by "hit5-x reaches
    # d = 8"; the other non-doubling sibling is hit2.
    for row in out:
        if row["x_cover_d"] == 8:
            label = "hit5"
        elif row["x_cover_d"] == 6 and row["y_cover_d"] == 6:
            label = "hit2"
        else:
            label = None
        for h in hits:
            if h["instance_id"] == row["instance_id"]:
                h["label"] = label
                print(f"labeled {row['instance_id']} = {label}")
    HITS_JSON.write_text(json.dumps(hits, indent=2))
    print(f"updated labels in {HITS_JSON}")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["hits", "ladders"])
    args = ap.parse_args()
    if args.cmd == "hits":
        recover_hits()
    else:
        run_ladders()


if __name__ == "__main__":
    main()
