"""A11 S3 — sector diagnosis + base-side safe-floor probe (engine frame).

Explains the presentation flip mechanically.  For a (hit, presentation,
axis) cell:

  diagnose   run the cover ladder, take the min-weight cover X-logical
             witness v, project p(v), and report which template sector it
             lives in: dangerous (p(v) ∈ Stab_Z(base), incl. 0 — the
             |b| + 2m(b) rung broke) or safe (p(v) a nontrivial base
             logical — the safe floor broke, with the class coset min).

  safefloor  the base-side (M-im)-style probe: coset-min ladders (SAT at
             n = 72, capped at 2d−1 = 11) over all 63 nonzero classes of
             im p_* mod base Z-stabilizers.  `safe_floor_ok` ⟺ every
             class min ≥ 12.  This is the T-c' surrogate for template
             condition 3's safe half — checkable WITHOUT any cover SAT.

Coset-min encoding: v ∈ rep + rowspace(HZb) ⟺ N·v = N·rep for
N = nullspace(HZb) (parities against the dual space), plus a sequential-
counter cardinality bound; ladder respects the coset's fixed weight
parity.  Everything discovery/validation (A_HANDOFF §1).

Usage:
    uv run python scripts/a11_s3_diagnose.py diagnose hit3:stored:x [more cells]
    uv run python scripts/a11_s3_diagnose.py safefloor hit3:anch36:x [more cells]
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

import numpy as np
from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195

LAB_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LAB_ROOT / "src"))
sys.path.insert(0, str(LAB_ROOT / "scripts"))

from bb_lab.checks import bb_check_matrices
from bb_lab.group import AbelianGroup
from bb_lab.linalg import nullspace_f2, rank_f2, rref_f2
from bb_lab.poly import Poly
from bb_lab.sat_distance import _xor_chain, find_logical_z, x_distance

from a9_lean_target_screen import blkdiag, cover_group, cover_maps, in_rowspace, lift_poly

DATA_DIR = LAB_ROOT / "data" / "a11"
HITS_JSON = DATA_DIR / "presentation_hits.json"
G6 = AbelianGroup((6, 6))


def load_cell(cell: str) -> tuple[str, str, str, Poly, Poly]:
    lab, pres, axis = cell.split(":")
    rec = {r["label"]: r for r in json.loads(HITS_JSON.read_text())}[lab]
    if pres == "stored":
        a_s, b_s = rec["stored_A"], rec["stored_B"]
    else:
        a_s, b_s = rec["anchorable"][int(pres.removeprefix("anch"))]
    return lab, pres, axis, Poly.from_string(a_s, G6), Poly.from_string(b_s, G6)


def coset_min_le(rep: np.ndarray, dual: np.ndarray, bound: int) -> np.ndarray | None:
    """SAT: is there v ∈ rep + rowspace(S) with |v| ≤ bound?  (`dual` =
    nullspace(S); membership ⟺ dual·v = dual·rep.)  Returns a witness or
    None."""
    n = rep.shape[0]
    pool = IDPool()
    qv = [pool.id() for _ in range(n)]
    cnf = CNF()
    rhs = (dual @ rep) % 2
    for row, r in zip(dual, rhs):
        idx = np.flatnonzero(row)
        out = _xor_chain((qv[i] for i in idx), pool, cnf)
        if out is None:
            continue
        cnf.append([out] if r else [-out])
    if bound < n:
        cnf.extend(CardEnc.atmost(lits=qv, bound=bound, vpool=pool,
                                  encoding=EncType.seqcounter).clauses)
    solver = Cadical195(bootstrap_with=cnf.clauses)
    try:
        if not solver.solve():
            return None
        model = solver.get_model()
        truth = {abs(l): l > 0 for l in model}
        return np.array([1 if truth.get(v, False) else 0 for v in qv], dtype=np.uint8)
    finally:
        solver.delete()


def coset_min(rep: np.ndarray, dual: np.ndarray, cap: int) -> int | None:
    """Exact coset min if ≤ cap, else None (meaning ≥ cap+1)."""
    parity = int(rep.sum() % 2)
    start = parity if parity else 2
    if (rep == 0).all():
        return 0
    for w in range(start, cap + 1, 2):
        if coset_min_le(rep, dual, w) is not None:
            return w
    return None


def safe_class_reps(A: Poly, B: Poly, axis: str):
    """Independent reps of im p_* mod base Z-stabilizers, plus HZb."""
    Gc = cover_group(6, 6, axis)
    chb = bb_check_matrices(A, B)
    chc = bb_check_matrices(lift_poly(A, Gc), lift_poly(B, Gc))
    HZb = chb.H_Z.astype(np.uint8)
    p_blk, _tau, _sig, _deck = cover_maps(G6, Gc, axis)
    P = blkdiag(p_blk)
    LZc = find_logical_z(chc)
    p_imgs = np.array([(P @ LZc[i]) % 2 for i in range(LZc.shape[0])], dtype=np.uint8)
    reps: list[np.ndarray] = []
    for i in range(p_imgs.shape[0]):
        stack = np.vstack([HZb] + ([np.array(reps)] if reps else []))
        if rank_f2(np.vstack([stack, p_imgs[i][None, :]])) > rank_f2(stack):
            reps.append(p_imgs[i])
    return np.array(reps, dtype=np.uint8), HZb, chb, chc


def run_diagnose(cells: list[str]) -> None:
    for cell in cells:
        lab, pres, axis, A, B = load_cell(cell)
        reps, HZb, chb, chc = safe_class_reps(A, B, axis)
        dual = nullspace_f2(HZb)
        t0 = time.time()
        res = x_distance(chc, weight_upper_bound=12)
        v = res.witness.astype(np.uint8)
        Gc = cover_group(6, 6, axis)
        p_blk, _t, _s, _d = cover_maps(G6, Gc, axis)
        pv = (blkdiag(p_blk) @ v) % 2
        w_pv = int(pv.sum())
        if not pv.any():
            sector = "dangerous (p(v) = 0: diagonal-type)"
        elif in_rowspace(HZb, pv):
            sector = f"dangerous (p(v) ∈ Stab_Z, |b| = {w_pv})"
        else:
            m = coset_min(pv, dual, 11)
            sector = (f"SAFE (p(v) nontrivial logical, |p(v)| = {w_pv}, "
                      f"class coset min = {m if m is not None else '>=12'})")
        print(f"{cell}: d_cover = {res.distance}, |v| = {int(v.sum())}, "
              f"sector: {sector}  ({time.time()-t0:.1f}s)", flush=True)


def run_safefloor(cells: list[str]) -> None:
    for cell in cells:
        lab, pres, axis, A, B = load_cell(cell)
        t0 = time.time()
        reps, HZb, chb, chc = safe_class_reps(A, B, axis)
        dual = nullspace_f2(HZb)
        r = reps.shape[0]
        minima: list[int | None] = []
        for mask in range(1, 1 << r):
            combo = np.zeros(reps.shape[1], dtype=np.uint8)
            for i in range(r):
                if (mask >> i) & 1:
                    combo ^= reps[i]
            minima.append(coset_min(combo, dual, 11))
        vals = ["≥12" if m is None else str(m) for m in minima]
        import collections
        hist = collections.Counter(vals)
        ok = all(m is None for m in minima)
        print(f"{cell}: rank(im p_*) = {r}, {len(minima)} classes, "
              f"minima histogram {dict(sorted(hist.items()))} -> "
              f"safe_floor_ok = {ok}  ({time.time()-t0:.1f}s)", flush=True)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["diagnose", "safefloor"])
    ap.add_argument("cells", nargs="+")
    args = ap.parse_args()
    if args.cmd == "diagnose":
        run_diagnose(args.cells)
    else:
        run_safefloor(args.cells)


if __name__ == "__main__":
    main()
