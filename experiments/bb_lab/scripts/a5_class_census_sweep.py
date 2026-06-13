"""A5 (goal 2) — (iv)/(v) census sweep over the empirical class.

Entry 3 proposed the class-theorem shape with two finite-verification
hypotheses replacing the presentation-bound coordinate kills:

  (iv) triangle censuses: for every dB-triangle class T with
       |B·T| = 3, B·T is not a translate of A; mirror for dA vs B.
  (v)  the (2,2) table is empty: A·{0,δ_L} ≠ t + B·{0,δ_R} for all
       δ_L, δ_R ≠ 0 and all t.

This script sweeps both over the empirical class (the Entry-1 members:
floor-bearing frame ∧ mult-free ∧ dA∩dB=∅, 25 on Z6xZ6 + 29 on
Z15xZ3) and reports who passes the FULL grid (a)–(d) — i.e. which
codes the class theorem covers today.

Floor verdicts:
  * Z6xZ6 members have (i) PASS ⟹ the A4 §3 Z₂²-engine floor ≥ 6
    (analytic).
  * Z15xZ3 members: floor = d_H(V_A)/d_H(V_B) (semisimple identity);
    reported together with the "pullback-friendly" flag (all vanishing
    characters of order 3 ⟹ the 5-fold-pullback-to-d₃ analytic route
    of Entry 4 applies verbatim).

All outputs discovery/validation only (A_HANDOFF §1).

Usage:  uv run python scripts/a5_class_census_sweep.py [--jsonl PATH]
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import sys
from pathlib import Path

LAB_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LAB_ROOT / "src"))

import duckdb
import numpy as np

from bb_lab.group import AbelianGroup
from bb_lab.linalg import nullspace_f2
from bb_lab.poly import Poly

_spec = importlib.util.spec_from_file_location(
    "a5_instance_hypotheses", LAB_ROOT / "scripts" / "a5_instance_hypotheses.py"
)
a5 = importlib.util.module_from_spec(_spec)
sys.modules["a5_instance_hypotheses"] = a5
_spec.loader.exec_module(a5)


def conv(G: AbelianGroup, p: frozenset, q: frozenset) -> frozenset:
    counts: dict[tuple[int, ...], int] = {}
    for a in p:
        for b in q:
            c = G.add(a, b)
            counts[c] = counts.get(c, 0) + 1
    return frozenset(c for c, k in counts.items() if k % 2)


def triangle_census(G: AbelianGroup, dS: frozenset) -> list[frozenset]:
    classes: set[frozenset] = set()
    for a in dS:
        for b in dS:
            if a == b:
                continue
            if G.sub(b, a) in dS:
                tri = frozenset([tuple(0 for _ in G.orders), a, b])
                cands = [frozenset(G.sub(t, mn) for t in tri) for mn in tri]
                classes.add(min(cands, key=lambda s: sorted(s)))
    return sorted(classes, key=lambda s: sorted(s))


def verdict_iv(G: AbelianGroup, A: Poly, B: Poly, dA: frozenset, dB: frozenset
               ) -> tuple[bool, int, int]:
    """(iv): no weight-3 triangle image is a translate of the partner."""
    elems = list(G)
    ok = True
    n13 = n31 = 0
    for tri in triangle_census(G, dB):
        img = conv(G, B.support, tri)
        if len(img) == 3:
            n13 += 1
            if any(frozenset(G.add(a, t) for a in A.support) == img
                   for t in elems):
                ok = False
    for tri in triangle_census(G, dA):
        img = conv(G, A.support, tri)
        if len(img) == 3:
            n31 += 1
            if any(frozenset(G.add(b, t) for b in B.support) == img
                   for t in elems):
                ok = False
    return ok, n13, n31


def verdict_v(G: AbelianGroup, A: Poly, B: Poly) -> bool:
    """(v): the (2,2) translate-match table is empty."""
    elems = list(G)
    zero = tuple(0 for _ in G.orders)
    nonzero = [g for g in elems if g != zero]
    # bucket right-side images by frozenset for O(1) lookup, keyed by size
    right: dict[int, set[frozenset]] = {}
    for dr in nonzero:
        base = conv(G, B.support, frozenset([zero, dr]))
        for t in elems:
            img = frozenset(G.add(c, t) for c in base)
            right.setdefault(len(img), set()).add(img)
    for dl in nonzero:
        sigL = conv(G, A.support, frozenset([zero, dl]))
        if sigL and sigL in right.get(len(sigL), set()):
            return False
    return True


def floor_data(rep) -> dict:
    """Per-frame one-sided floor data."""
    if rep.frame.shape == "Z2xZ2":
        # (i) PASS ⟹ A4 §3 engine floor ≥ 6, analytic
        return {"floor_route": "Z2xZ2-engine", "floor_ok": rep.verdict_i}
    if rep.frame.shape == "semisimple":
        fields = a5.orbit_fields(rep.frame.odd_orders)
        H = AbelianGroup(rep.frame.odd_orders)
        elems = list(H)
        n = len(elems)

        def dH(zero_orbits: set) -> int | None:
            rows = []
            for of in fields:
                if of.rep in zero_orbits:
                    continue
                for i in range(of.r):
                    rows.append(
                        [of.alpha_powers[of.psi_exp(t)][i] for t in elems]
                    )
            basis = nullspace_f2(np.array(rows, dtype=np.uint8))
            k = basis.shape[0]
            if k == 0 or k > 18:
                return None
            best = n + 1
            for mask in range(1, 2**k):
                v = np.zeros(n, dtype=np.uint8)
                mm, i = mask, 0
                while mm:
                    if mm & 1:
                        v ^= basis[i]
                    mm >>= 1
                    i += 1
                w = int(v.sum())
                if 0 < w < best:
                    best = w
            return best

        V_A = {c.orbit_rep for c in rep.comps_A if c.kind == a5.ZERO}
        V_B = {c.orbit_rep for c in rep.comps_B if c.kind == a5.ZERO}
        fA, fB = dH(V_A), dH(V_B)
        # pullback-friendly: every vanishing character has order 3
        odd = rep.frame.odd_orders

        def order3(k: tuple) -> bool:
            from math import gcd, lcm
            d = 1
            for ki, no in zip(k, odd):
                if ki:
                    d = lcm(d, no // gcd(ki, no))
            return d == 3

        pb = all(order3(k) for k in (V_A | V_B))
        return {
            "floor_route": "semisimple-dH",
            "floor_A": fA,
            "floor_B": fB,
            "floor_ok": fA is not None and fB is not None
            and min(fA, fB) >= 6,
            "pullback_friendly": pb,
        }
    return {"floor_route": rep.frame.shape, "floor_ok": False}


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--jsonl", type=Path, default=None)
    args = ap.parse_args()

    con = duckdb.connect(str(LAB_ROOT / "data" / "bb_instances.duckdb"),
                         read_only=True)
    rows = con.execute(
        "select instance_id, ell, m, A_poly, B_poly, n, k, d_exact "
        "from bb_instances where group_struct in ('Z6xZ6', 'Z15xZ3') "
        "and d_exact is not null order by group_struct, instance_id"
    ).fetchall()

    out_f = args.jsonl.open("w") if args.jsonl else None
    members = []
    for iid, ell, m, A_s, B_s, n, k, d_exact in rows:
        rep = a5.check_instance(iid, ell, m, A_s, B_s)
        d_ = rep.diff
        if not (d_.dA_mult_free and d_.dB_mult_free and d_.disjoint):
            continue
        # frame-level class membership (Entry 1): floor-bearing frame +
        # (i) on Z2xZ2 frames
        if rep.frame.shape == "Z2xZ2" and not rep.verdict_i:
            continue
        if rep.frame.shape not in ("Z2xZ2", "semisimple"):
            continue
        G = AbelianGroup((ell, m))
        A = Poly.from_string(A_s, G)
        B = Poly.from_string(B_s, G)
        iv, n13, n31 = verdict_iv(G, A, B, d_.dA, d_.dB)
        v = verdict_v(G, A, B)
        fd = floor_data(rep)
        full = fd["floor_ok"] and iv and v
        row = {
            "label": iid, "group": f"Z{ell}xZ{m}", "k": k,
            "d_exact": d_exact, "frame": rep.frame.shape,
            "iv": iv, "n_tri_13": n13, "n_tri_31": n31, "v": v,
            "full_grid_pass": full, **fd,
        }
        members.append(row)
        if out_f:
            out_f.write(json.dumps(row) + "\n")
    if out_f:
        out_f.close()

    print(f"# empirical class members swept: {len(members)}")
    from collections import Counter

    by = Counter((r["group"], r["full_grid_pass"]) for r in members)
    for key, cnt in sorted(by.items(), key=str):
        print(f"  {key}: {cnt}")
    print("\n# full-grid passes (class theorem covers these today):")
    for r in members:
        if r["full_grid_pass"]:
            extra = (f" floors=({r.get('floor_A')},{r.get('floor_B')})"
                     f" pb={r.get('pullback_friendly')}"
                     if r["frame"] == "semisimple" else "")
            print(f"  {r['label'][:10]} {r['group']} k={r['k']} "
                  f"d={r['d_exact']} frame={r['frame']}{extra}")
    print("\n# failures by hypothesis among members:")
    fails = Counter()
    for r in members:
        if not r["floor_ok"]:
            fails["floor"] += 1
        if not r["iv"]:
            fails["iv"] += 1
        if not r["v"]:
            fails["v"] += 1
    print(f"  {dict(fails)}")


if __name__ == "__main__":
    main()
