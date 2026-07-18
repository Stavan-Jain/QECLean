"""A11 S1 — the A8 hypothesis audit on the engine frame (Z6xZ6).

Regenerates the A9 T2 presentation-anchorable census (the uncommitted
`data/a9/t2_presentation_hits.json` — the committed `t2` subcommand only
does the raw census), then evaluates the homotopy-certificate hierarchy
of `notes/A11_literal_lift_criterion.md` §1 on every audit cell:

    R0-sq  ∃ univariate q(t): q·P² = 1+δ    (A8's squaring-identity shape)
    R0     1+δ ∈ (P)                         (single-generator ideal)
    R1     1+δ ∈ (A, B)                      (two-generator ideal)
    sq2    1+δ ∈ (A², B²)                    (the layer's sq-ideal route)
    R2     σ_* = id on H₁(cover)             (the property itself)

plus the literal gross-shape identity `(1+t²)P² = 1+δ`, linchpin,
`dim ker ∂₂`, μ(Ann A/B), k(cover), the tight diagonal witness, and the
anchorability verdicts (i)/(ii)/(iii).

**Presentation discipline** (found the hard way, 2026-07-02): the A9 T2
cover ladders ran on the STORED corpus forms — which are NOT anchorable
presentations (their `B` is monomial in neither axis; verdict (iii)
fails).  The A8 hypotheses instead hold, if anywhere, on the Aut×swap
orbit's anchorable points.  So each hit class gets two kinds of cells:

    stored:<axis>   the corpus form — comparable to the A9 ladder verdicts
    anch<i>:<axis>  the i-th anchorable presentation (0-indexed into the
                    hits JSON list) — where A8's hypotheses live

The audit computes cheap features on ALL cells, groups anchorable cells
by cheap-feature signature, and runs the expensive features (R2,
linchpin, k_cover, tight witness) on stored cells + one representative
per signature group.  Safe-class coset minima and the ≤ 2d−1 boundary
census are NOT computed — both need 2^rank(∂₂) ≈ 2^34 span sweeps at 36
cells (the A9 T1 columns exist only because those frames have ≤ 24 cells).

Everything here is discovery/validation (A_HANDOFF §1).

Subcommands:
    uv run python scripts/a11_s1_audit.py hits    [--db PATH]
    uv run python scripts/a11_s1_audit.py audit
    uv run python scripts/a11_s1_audit.py ladders [--cells hit1:stored:x,hit3:anch0:y,...]
    uv run python scripts/a11_s1_audit.py baseline

`hits` and `audit` are fast (minutes, no SAT).  `ladders` runs exact SAT
distance on the requested cells' covers (n = 144): cheap when the verdict
is a low-weight witness, UNSAT-to-11 (tens of minutes) when the cover
doubles; JSONL-resumable (reruns skip recorded cells).  `baseline`
reproduces the plan's S0 spot checks (the Lean-proven Z3Z6 pair and one
A9 T1 row) — run it once before quoting anything else.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

import numpy as np

LAB_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LAB_ROOT / "src"))
sys.path.insert(0, str(LAB_ROOT / "scripts"))

from bb_lab.automorphism import automorphisms
from bb_lab.canonical import build_perm_table, canonical_pair
from bb_lab.checks import bb_check_matrices, circulant
from bb_lab.codeparams import code_params
from bb_lab.group import AbelianGroup
from bb_lab.linalg import nullspace_f2, quotient_complement_basis, rank_f2
from bb_lab.poly import Poly
from bb_lab.sat_distance import _solve_at_weight, find_logical_z, x_distance

from a5_cover_cascade import evaluate, is_anchorable
from a5_instance_hypotheses import diff_set_report, projection_report
from a9_lean_target_screen import (
    blkdiag,
    cover_group,
    cover_maps,
    in_rowspace,
    lift_poly,
    min_weight_in_span,
    sq_ideal_solve,
    tight_witness_check,
)

DATA_DIR = LAB_ROOT / "data" / "a11"
HITS_JSON = DATA_DIR / "presentation_hits.json"
HITS_JSON_A9_COMPAT = LAB_ROOT / "data" / "a9" / "t2_presentation_hits.json"
AUDIT_JSON = DATA_DIR / "s1_audit.json"
LADDERS_JSONL = DATA_DIR / "s1_ladders.jsonl"

G6 = AbelianGroup((6, 6))

# Labels verified against the A9 note's quoted stored forms (2026-07-02):
# hit3 stored B = y+x*y^2+x^2, hit4 = y^2+x*y^3+x^2*y, hit6 = x*y+x^2*y^2+x^3,
# hit1 = the gross-base class.  The remaining two ids are hit2/hit5, told
# apart by their x-cover ladder verdicts (A9: hit2-x stays 6, hit5-x = 8).
ID_LABELS = {
    "5620b8e2c34acc75": "hit1",
    "9b9581f986a0d0ac": "hit3",
    "8b3fe87db2da2b48": "hit4",
    "702393fa5fd7449c": "hit6",
}

CHEAP_KEYS = [
    "dim_ker_d2", "dim_annA", "dim_annB", "mu_annA", "mu_annB",
    "anch_i", "anch_ii", "anch_iii", "anchorable",
    "A8exact_A", "A8exact_B", "R0sq_A", "R0sq_B",
    "R0lin_univ_A", "R0lin_univ_B", "R0_A", "R0_B",
    "sq2_A", "sq2_B", "sq2_both", "sq2_q1zero", "R1",
]
EXPENSIVE_KEYS = ["k_cover", "R2_homotopy", "linchpin", "tight_witness"]


def poly_str(support: frozenset[tuple[int, ...]]) -> str:
    terms = []
    for a, b in sorted(support):
        parts = []
        if a:
            parts.append("x" if a == 1 else f"x^{a}")
        if b:
            parts.append("y" if b == 1 else f"y^{b}")
        terms.append("*".join(parts) if parts else "1")
    return " + ".join(terms)


def quick_anchorable(P: Poly, Q: Poly, G: AbelianGroup) -> bool:
    """Cheap-gates-first version of a5's is_anchorable (identical verdict)."""
    if len(P.support) != 3 or len(Q.support) != 3:
        return False
    if not projection_report(P, Q, G).verdict:
        return False
    if not diff_set_report(P, Q, G).verdict:
        return False
    return is_anchorable(evaluate("probe", G, P, Q))


# ---------------------------------------------------------------------------
# hits — the presentation-orbit census
# ---------------------------------------------------------------------------


def find_hits(db_path: Path) -> None:
    import duckdb

    con = duckdb.connect(str(db_path), read_only=True)
    rows = con.execute(
        "SELECT instance_id, A_poly, B_poly, k, d_exact FROM bb_instances "
        "WHERE group_struct = 'Z6xZ6' AND k > 0 AND d_exact >= 6 "
        "ORDER BY instance_id"
    ).fetchall()
    con.close()
    print(f"Z6xZ6 corpus, k>0, d>=6: {len(rows)} codes", flush=True)

    auts = automorphisms(G6)
    perms = build_perm_table(G6, auts=auts)
    t0 = time.time()
    found: list[dict] = []
    for n_done, (iid, A_str, B_str, k, d) in enumerate(rows, 1):
        A = Poly.from_string(A_str, G6)
        B = Poly.from_string(B_str, G6)
        anch: list[tuple[frozenset, frozenset]] = []
        seen: set[tuple[frozenset, frozenset]] = set()
        for phi in auts:
            As, Bs = phi.apply_support(A.support), phi.apply_support(B.support)
            for Ps, Qs in ((As, Bs), (Bs, As)):
                if (Ps, Qs) in seen:
                    continue
                seen.add((Ps, Qs))
                if quick_anchorable(Poly(support=Ps, group=G6), Poly(support=Qs, group=G6), G6):
                    anch.append((Ps, Qs))
        if anch:
            can = canonical_pair(A.support, B.support, G6, auts=auts, perms=perms)
            found.append({
                "instance_id": iid, "stored_A": A_str, "stored_B": B_str,
                "k": k, "d": d,
                "canonical_key": can.key,
                "anchorable": sorted(
                    (poly_str(p), poly_str(q)) for p, q in anch),
            })
            print(f"  ANCHORABLE {iid} k={k} d={d} ({len(anch)} presentations)", flush=True)
        if n_done % 100 == 0:
            print(f"  [{n_done}/{len(rows)}] {time.time()-t0:.0f}s", flush=True)

    classes: dict[tuple, list[dict]] = {}
    for rec in found:
        classes.setdefault(tuple(rec["canonical_key"]), []).append(rec)
    print(f"{len(found)} anchorable codes in {len(classes)} equivalence classes", flush=True)

    out = []
    unlabeled = 0
    for key, recs in sorted(classes.items(), key=lambda kv: kv[1][0]["instance_id"]):
        label = None
        for r in recs:
            label = label or ID_LABELS.get(r["instance_id"])
        if label is None:
            unlabeled += 1
            label = f"hitU{unlabeled}"  # ladder verdicts map these to hit2/hit5
        all_anch = sorted({tuple(pq) for r in recs for pq in r["anchorable"]})
        out.append({
            "label": label,
            "instance_ids": [r["instance_id"] for r in recs],
            "k": recs[0]["k"], "d": recs[0]["d"],
            "stored_A": recs[0]["stored_A"], "stored_B": recs[0]["stored_B"],
            "n_anchorable_presentations": len(all_anch),
            "anchorable": [list(pq) for pq in all_anch],
        })

    DATA_DIR.mkdir(parents=True, exist_ok=True)
    HITS_JSON.write_text(json.dumps(out, indent=1))
    HITS_JSON_A9_COMPAT.parent.mkdir(parents=True, exist_ok=True)
    HITS_JSON_A9_COMPAT.write_text(json.dumps(out, indent=1))
    for rec in out:
        print(f"  {rec['label']}: ids={rec['instance_ids']} d={rec['d']} "
              f"stored A=`{rec['stored_A']}` B=`{rec['stored_B']}` "
              f"({rec['n_anchorable_presentations']} anchorable presentations)")
    print(f"wrote {HITS_JSON} (+ a9-compat copy)")


# ---------------------------------------------------------------------------
# audit — the certificate hierarchy per cell
# ---------------------------------------------------------------------------


def solvable(cols: np.ndarray, target: np.ndarray) -> bool:
    return rank_f2(cols.T) == rank_f2(np.vstack([cols.T, target[None, :]]))


def cheap_features(A: Poly, B: Poly, axis: str) -> dict:
    Gc = cover_group(6, 6, axis)
    Ac, Bc = lift_poly(A, Gc), lift_poly(B, Gc)
    MA, MB = circulant(A).astype(np.uint8), circulant(B).astype(np.uint8)
    out: dict = {}

    kerd2 = nullspace_f2(np.vstack([MA, MB]) % 2)
    out["dim_ker_d2"] = int(kerd2.shape[0])
    for name, M in (("annA", MA), ("annB", MB)):
        ann = nullspace_f2(M)
        out[f"dim_{name}"] = int(ann.shape[0])
        if ann.shape[0] <= 22:
            out[f"mu_{name}"] = min_weight_in_span(ann)
        else:  # basis min only (flagged by dim > 22)
            w = ann.sum(axis=1)
            out[f"mu_{name}"] = int(w[w > 0].min()) if (w > 0).any() else None

    rep = evaluate("audit", G6, A, B)
    out["anch_i"], out["anch_ii"], out["anch_iii"] = (
        rep.verdict_i, rep.verdict_ii, rep.verdict_iii)
    out["anchorable"] = is_anchorable(rep)

    deck = (6, 0) if axis == "x" else (0, 6)
    nc = Gc.cardinality
    target = np.zeros(nc, dtype=np.uint8)
    target[Gc.index((0, 0))] ^= 1
    target[Gc.index(deck)] ^= 1

    MAc = circulant(Ac).astype(np.uint8)
    MBc = circulant(Bc).astype(np.uint8)
    MAc2, MBc2 = (MAc @ MAc) % 2, (MBc @ MBc) % 2
    univ_idx = ([Gc.index((j, 0)) for j in range(Gc.orders[0])] if axis == "x"
                else [Gc.index((0, j)) for j in range(Gc.orders[1])])
    # the literal gross-shape multiplier 1 + t^2
    q_gross = np.zeros(nc, dtype=np.uint8)
    q_gross[Gc.index((0, 0))] ^= 1
    q_gross[Gc.index((2, 0) if axis == "x" else (0, 2))] ^= 1

    out["A8exact_A"] = bool((((MAc2 @ q_gross) % 2) == target).all())
    out["A8exact_B"] = bool((((MBc2 @ q_gross) % 2) == target).all())
    out["R0sq_A"] = solvable(MAc2[:, univ_idx], target)
    out["R0sq_B"] = solvable(MBc2[:, univ_idx], target)
    out["R0lin_univ_A"] = solvable(MAc[:, univ_idx], target)
    out["R0lin_univ_B"] = solvable(MBc[:, univ_idx], target)
    out["R0_A"] = solvable(MAc, target)
    out["R0_B"] = solvable(MBc, target)
    out["sq2_A"] = solvable(MAc2, target)
    out["sq2_B"] = solvable(MBc2, target)
    out["R1"] = solvable(np.hstack([MAc, MBc]), target)
    sq_both, sq_q1zero = sq_ideal_solve(Ac, Bc, Gc, deck)
    out["sq2_both"] = sq_both
    out["sq2_q1zero"] = sq_q1zero
    return out


def expensive_features(A: Poly, B: Poly, axis: str) -> dict:
    Gc = cover_group(6, 6, axis)
    Ac, Bc = lift_poly(A, Gc), lift_poly(B, Gc)
    chb, chc = bb_check_matrices(A, B), bb_check_matrices(Ac, Bc)
    HXb, HZb = chb.H_X.astype(np.uint8), chb.H_Z.astype(np.uint8)
    HXc, HZc = chc.H_X.astype(np.uint8), chc.H_Z.astype(np.uint8)
    out: dict = {"k_cover": code_params(chc).k}

    p_blk, tau_blk, sig_blk, _deck = cover_maps(G6, Gc, axis)
    P, T, S = blkdiag(p_blk), blkdiag(tau_blk), blkdiag(sig_blk)
    LZc = find_logical_z(chc)
    out["R2_homotopy"] = all(
        in_rowspace(HZc, ((S @ LZc[i]) % 2) ^ LZc[i]) for i in range(LZc.shape[0]))
    out["linchpin"] = all(
        in_rowspace(HZc, (T @ ((P @ LZc[i]) % 2)) % 2) for i in range(LZc.shape[0]))

    LXb = quotient_complement_basis(HXb, nullspace_f2(HZb))
    wit, _ = _solve_at_weight(HXb, LXb, 6)
    out["tight_witness"] = bool(
        wit is not None
        and tight_witness_check(G6, (wit & 1).astype(np.uint8), tau_blk, HZc, HXc))
    return out


def run_audit() -> None:
    hits = json.loads(HITS_JSON.read_text())
    cells: list[dict] = []
    for rec in hits:
        label = rec["label"]
        presentations = [("stored", rec["stored_A"], rec["stored_B"])] + [
            (f"anch{i}", a, b) for i, (a, b) in enumerate(rec["anchorable"])]
        for axis in ("x", "y"):
            sig_reps: dict[tuple, str] = {}
            for pres, a_s, b_s in presentations:
                t0 = time.time()
                A, B = Poly.from_string(a_s, G6), Poly.from_string(b_s, G6)
                cell = {"label": label, "pres": pres, "axis": axis, "A": a_s, "B": b_s}
                cell.update(cheap_features(A, B, axis))
                sig = tuple(cell[k] for k in CHEAP_KEYS)
                if pres == "stored" or sig not in sig_reps:
                    cell.update(expensive_features(A, B, axis))
                    if pres != "stored":
                        sig_reps[sig] = pres
                    cell["sig_rep"] = cell["pres"]
                else:
                    cell["sig_rep"] = sig_reps[sig]
                cells.append(cell)
                if pres == "stored" or cell["sig_rep"] == pres:
                    print(f"  {label}:{pres}:{axis}  "
                          f"anch={'Y' if cell['anchorable'] else 'N'} "
                          f"kerd2={cell['dim_ker_d2']} "
                          f"A8ex(A/B)={'Y' if cell['A8exact_A'] else 'N'}/{'Y' if cell['A8exact_B'] else 'N'} "
                          f"R0sq={'Y' if cell['R0sq_A'] else 'N'}/{'Y' if cell['R0sq_B'] else 'N'} "
                          f"R0={'Y' if cell['R0_A'] else 'N'}/{'Y' if cell['R0_B'] else 'N'} "
                          f"sq2both={'Y' if cell['sq2_both'] else 'N'} "
                          f"R1={'Y' if cell['R1'] else 'N'} "
                          f"R2={'Y' if cell.get('R2_homotopy') else 'N'} "
                          f"k_cov={cell.get('k_cover')} "
                          f"({time.time()-t0:.1f}s)", flush=True)
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    AUDIT_JSON.write_text(json.dumps(cells, indent=1))
    n_full = sum(1 for c in cells if "k_cover" in c)
    print(f"wrote {AUDIT_JSON}: {len(cells)} cells ({n_full} with expensive features)")


# ---------------------------------------------------------------------------
# ladders — exact SAT verdicts on selected cells
# ---------------------------------------------------------------------------


def run_ladders(cells: list[str] | None) -> None:
    hits = {r["label"]: r for r in json.loads(HITS_JSON.read_text())}
    if cells is None:
        cells = [f"{lab}:stored:{ax}" for lab in sorted(hits) for ax in ("x", "y")]
    done: set[str] = set()
    if LADDERS_JSONL.exists():
        for line in LADDERS_JSONL.open():
            r = json.loads(line)
            done.add(f"{r['label']}:{r['pres']}:{r['axis']}")
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    with LADDERS_JSONL.open("a") as fh:
        for cell in cells:
            if cell in done:
                print(f"  {cell}: already recorded, skipping", flush=True)
                continue
            lab, pres, axis = cell.split(":")
            rec = hits[lab]
            if pres == "stored":
                a_s, b_s = rec["stored_A"], rec["stored_B"]
            else:
                a_s, b_s = rec["anchorable"][int(pres.removeprefix("anch"))]
            Gc = cover_group(6, 6, axis)
            A, B = Poly.from_string(a_s, G6), Poly.from_string(b_s, G6)
            chc = bb_check_matrices(lift_poly(A, Gc), lift_poly(B, Gc))
            row = {"label": lab, "pres": pres, "axis": axis, "A": a_s, "B": b_s,
                   "k_cover": code_params(chc).k}
            t0 = time.time()
            try:
                res = x_distance(chc, weight_upper_bound=12)
                row["d_cover"] = res.distance
            except RuntimeError:
                row["d_cover"] = ">12"
            row["seconds"] = round(time.time() - t0, 1)
            fh.write(json.dumps(row) + "\n")
            fh.flush()
            print(f"  {cell}: k={row['k_cover']} d_cover={row['d_cover']} "
                  f"({row['seconds']}s)", flush=True)


# ---------------------------------------------------------------------------
# baseline — the plan's S0 spot checks
# ---------------------------------------------------------------------------


def run_baseline() -> None:
    # 1. the Lean-proven Z3Z6 pair: [[36,4,4]] -x-> [[72,4,8]]
    Gb = AbelianGroup((3, 6))
    A = Poly.from_string("x^2 + y + y^3", Gb)
    B = Poly.from_string("1 + x + y^2", Gb)
    d_base = x_distance(bb_check_matrices(A, B), weight_upper_bound=8).distance
    Gc = cover_group(3, 6, "x")
    d_cov = x_distance(
        bb_check_matrices(lift_poly(A, Gc), lift_poly(B, Gc)), weight_upper_bound=12
    ).distance
    ok1 = (d_base, d_cov) == (4, 8)
    print(f"baseline 1 (Z3Z6 doc pair): d_base={d_base} d_cover={d_cov} "
          f"{'PASS' if ok1 else 'FAIL'}")
    # 2. one A9 T1 row: Z3xZ6 y-cover, A=1+y+y^2, B=y+x*y+x*y^3 -> d 4->8
    A2 = Poly.from_string("1 + y + y^2", Gb)
    B2 = Poly.from_string("y + x*y + x*y^3", Gb)
    d2b = x_distance(bb_check_matrices(A2, B2), weight_upper_bound=8).distance
    Gc2 = cover_group(3, 6, "y")
    d2c = x_distance(
        bb_check_matrices(lift_poly(A2, Gc2), lift_poly(B2, Gc2)), weight_upper_bound=12
    ).distance
    ok2 = (d2b, d2c) == (4, 8)
    print(f"baseline 2 (A9 T1 row 12): d_base={d2b} d_cover={d2c} "
          f"{'PASS' if ok2 else 'FAIL'}")
    if not (ok1 and ok2):
        sys.exit(1)


# ---------------------------------------------------------------------------


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["hits", "audit", "ladders", "baseline"])
    ap.add_argument("--db", type=Path,
                    default=LAB_ROOT / "data" / "bb_instances.duckdb")
    ap.add_argument("--cells", type=str, default=None,
                    help="comma-separated label:pres:axis cells for `ladders`")
    args = ap.parse_args()
    if args.cmd == "hits":
        find_hits(args.db)
    elif args.cmd == "audit":
        run_audit()
    elif args.cmd == "ladders":
        run_ladders(args.cells.split(",") if args.cells else None)
    else:
        run_baseline()


if __name__ == "__main__":
    main()
