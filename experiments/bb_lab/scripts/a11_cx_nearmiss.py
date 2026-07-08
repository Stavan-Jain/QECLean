"""A11 CX — S2 near-miss probe: dangerous-rung shadow margins on C-safe cells.

For each C-safe-true cell (frame, A, B, axis) from the hunt stream, probe the
ONLY unproven piece of "C-safe => doubling" (A11 Entry 2/2b): the light-b
dangerous rung.  On the DUAL complex (x_distance witnesses are X-type, in
ker H_Z; dangerous projections land in rowspace(H_X^base)):

  * enumerate light dual stabilizers b (rows of H_X^base, 2-row and 3-row
    sums), 0 < |b| < 2d;
  * solve d2 y = b (d2 = H_X^base^T), greedily reduce the seam pair
    (h, h') = (d2c y, d2nc y) over the ker d2 coset;
  * Sigma(b) = supp(h) | supp(h'); for every nontrivial base X-logical class
    (relaxation of the tau-fiber: only makes violations easier to find),
    compute the Sigma-punctured coset minimum m_out = min |rho restricted
    outside Sigma| by SAT (coset membership + cardinality on the complement).

Prop D4:  slice(b) >= |b| + 2*m_out, so the rung over b is FREE whenever
margin(b) := m_out - (d - |b|/2) >= 0.  A cell whose minimal margin is
negative is a NEAR-VIOLATION of the shadow bound (the rung itself may still
hold via cancellation structure — but these are the cells to attack).  On a
C-safe-true cell with confirmed d(cover) = 2d the negative margin is
diagnostic slack only; on an unladdered one it is a priority flag.

Validation: inline V1-style asserts (d2nc + d2c == base d2; block form
reconstructs the cover d2), plus the Z3Z6 Lean-proven control.

Usage:
    uv run python scripts/a11_cx_nearmiss.py control
    uv run python scripts/a11_cx_nearmiss.py sweep [--files a,b] [--limit N]
        [--out data/a11/cx/nearmiss.jsonl]
"""

from __future__ import annotations

import argparse
import itertools
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
from bb_lab.linalg import nullspace_f2, quotient_complement_basis
from bb_lab.poly import Poly
from bb_lab.sat_distance import _xor_chain

from a9_lean_target_screen import cover_group, lift_poly
from a11_s4_dangerous_reduction import sheet_maps

CX_DIR = LAB_ROOT / "data" / "a11" / "cx"


# ---------------------------------------------------------------------------
# dual-complex sheet split (V1 machinery, dual side)
# ---------------------------------------------------------------------------


def dual_sheet_split(ell: int, m: int, axis: str, A: Poly, B: Poly):
    """Return (d2b, d2nc, d2cc, Q, chb, chc, Gb) for the DUAL complex
    (d2 = H_X^T: 2-cells = X-checks = group cells -> qubits)."""
    Gb, Gc, S, Q = sheet_maps(ell, m, axis)
    nb = Gb.cardinality
    chb = bb_check_matrices(A, B)
    chc = bb_check_matrices(lift_poly(A, Gc), lift_poly(B, Gc))
    d2b = chb.H_X.astype(np.uint8).T          # (2nb x nb)
    d2c_full = chc.H_X.astype(np.uint8).T     # (2nc x nc)
    d2nc = np.zeros((2 * nb, nb), dtype=np.uint8)
    d2cc = np.zeros((2 * nb, nb), dtype=np.uint8)
    inv_q = {}
    for s in (0, 1):
        for i, qi in enumerate(Q[s]):
            inv_q[qi] = (s, i)
    for j in range(nb):
        col = d2c_full[:, S[0, j]]
        for qi in np.flatnonzero(col):
            s, i = inv_q[qi]
            (d2nc if s == 0 else d2cc)[i, j] ^= 1
    # V1-style inline validation
    assert ((d2nc ^ d2cc) == d2b).all(), "sheet split does not sum to base d2"
    recon = np.zeros_like(d2c_full)
    ncell = Gc.cardinality
    for j in range(nb):
        for s in (0, 1):
            colv = np.zeros(2 * ncell, dtype=np.uint8)
            colv[Q[s]] ^= d2nc[:, j]
            colv[Q[1 - s]] ^= d2cc[:, j]
            recon[:, S[s, j]] = colv
    assert (recon == d2c_full).all(), "block form fails to reconstruct cover d2"
    return d2b, d2nc, d2cc, chb, chc, Gb


def solve_f2(M: np.ndarray, b: np.ndarray) -> np.ndarray | None:
    """One solution of M y = b over F2 (M: rows x cols), or None."""
    rows, cols = M.shape
    Maug = np.concatenate([M % 2, b[:, None] % 2], axis=1).astype(np.uint8)
    piv_cols, r = [], 0
    for c in range(cols):
        pr = next((rr for rr in range(r, rows) if Maug[rr, c]), None)
        if pr is None:
            continue
        Maug[[r, pr]] = Maug[[pr, r]]
        for rr in range(rows):
            if rr != r and Maug[rr, c]:
                Maug[rr] ^= Maug[r]
        piv_cols.append(c)
        r += 1
    for rr in range(r, rows):
        if not Maug[rr, :-1].any() and Maug[rr, -1]:
            return None
    y = np.zeros(cols, dtype=np.uint8)
    for i, c in enumerate(piv_cols):
        y[c] = Maug[i, -1]
    return y


def greedy_seam_reduce(y: np.ndarray, ker2: np.ndarray, d2nc: np.ndarray,
                       d2cc: np.ndarray, passes: int = 4) -> np.ndarray:
    """Greedy |h| + |h'| reduction over y + ker d2."""
    def cost(yy: np.ndarray) -> int:
        return int(((d2cc @ yy) % 2).sum() + ((d2nc @ yy) % 2).sum())

    best, bc = y.copy(), cost(y)
    for _ in range(passes):
        improved = False
        for z in ker2:
            cand = (best ^ z).astype(np.uint8)
            cc = cost(cand)
            if cc < bc:
                best, bc, improved = cand, cc, True
        if not improved:
            break
    return best


# ---------------------------------------------------------------------------
# punctured coset minimum (SAT)
# ---------------------------------------------------------------------------


def punctured_coset_min(rep: np.ndarray, dual: np.ndarray, outside: np.ndarray,
                        cap: int) -> int | None:
    """min over v in rep + rowspace(S) of |v restricted to `outside`| if <= cap
    else None.  `dual` = nullspace(S); `outside` = boolean mask."""
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
    out_lits = [qv[i] for i in np.flatnonzero(outside)]
    for w in range(0, cap + 1):
        c2 = CNF(from_clauses=cnf.clauses)
        if w < len(out_lits):
            c2.extend(CardEnc.atmost(lits=out_lits, bound=w, vpool=pool,
                                     encoding=EncType.seqcounter).clauses)
        solver = Cadical195(bootstrap_with=c2.clauses)
        try:
            if solver.solve():
                return w
        finally:
            solver.delete()
    return None


# ---------------------------------------------------------------------------
# per-cell rung margins
# ---------------------------------------------------------------------------


def light_duals(HXb: np.ndarray, two_d: int, max_terms: int = 3,
                max_b: int = 400) -> list[np.ndarray]:
    """Light dual stabilizers: sums of up to `max_terms` rows of H_X^base with
    0 < |b| < 2d, deduped."""
    rows = HXb % 2
    seen: dict[bytes, np.ndarray] = {}
    nr = rows.shape[0]
    for t in range(1, max_terms + 1):
        for comb in itertools.combinations(range(nr), t):
            b = np.zeros(rows.shape[1], dtype=np.uint8)
            for i in comb:
                b ^= rows[i]
            w = int(b.sum())
            if 0 < w < two_d:
                seen.setdefault(b.tobytes(), b)
            if len(seen) >= max_b:
                return list(seen.values())
    return list(seen.values())


def cell_margins(frame: tuple[int, int], a_s: str, b_s: str, axis: str,
                 d: int, class_cap: int = 8) -> dict:
    ell, m = frame
    Gb0 = AbelianGroup((ell, m))
    A = Poly.from_string(a_s, Gb0)
    B = Poly.from_string(b_s, Gb0)
    t0 = time.time()
    d2b, d2nc, d2cc, chb, chc, Gb = dual_sheet_split(ell, m, axis, A, B)
    HXb = chb.H_X.astype(np.uint8)
    HZb = chb.H_Z.astype(np.uint8)
    ker2 = nullspace_f2(d2b) % 2                       # ker d2 (dual 2-cells)
    dualX = nullspace_f2(HXb)                          # coset dual for rowspace(HXb)
    # nontrivial X-logical class reps: span of LXb mod rowspace(HXb)
    LXb = quotient_complement_basis(HXb, nullspace_f2(HZb))
    k = LXb.shape[0]
    rec: dict = {"frame": f"Z{ell}xZ{m}", "A": a_s, "B": b_s, "axis": axis,
                 "d_base": d, "k": int(k)}
    if k > class_cap:
        rec["skip"] = "k_too_big"
        return rec
    bs = light_duals(HXb, 2 * d)
    rec["n_light_b"] = len(bs)
    worst = None
    for b in bs:
        y = solve_f2(d2b, b)
        if y is None:      # b not in im d2 — cannot happen for rowspace sums
            continue
        y = greedy_seam_reduce(y, ker2, d2nc, d2cc)
        h = (d2cc @ y) % 2
        hp = (d2nc @ y) % 2
        sigma = (h | hp).astype(bool)
        outside = ~sigma
        need = d - (int(b.sum()) // 2)        # rung free if m_out >= d - |b|/2
        cap = max(need, 0)
        m_out_min = None
        for mask in range(1, 1 << k):
            rep = np.zeros(HXb.shape[1], dtype=np.uint8)
            for i in range(k):
                if (mask >> i) & 1:
                    rep ^= LXb[i] % 2
            m_out = punctured_coset_min(rep, dualX, outside, cap)
            v = cap + 1 if m_out is None else m_out
            if m_out_min is None or v < m_out_min:
                m_out_min = v
            if m_out_min == 0:
                break
        # margin measured with ceiling at cap+1 ("> need" == comfortably free)
        margin = m_out_min - need
        item = {"b_weight": int(b.sum()), "sigma": int(sigma.sum()),
                "m_out_min": int(m_out_min), "need": int(need),
                "margin": int(margin)}
        if worst is None or item["margin"] < worst["margin"]:
            worst = item
    rec["worst_rung"] = worst
    rec["t"] = round(time.time() - t0, 1)
    return rec


# ---------------------------------------------------------------------------


def control() -> None:
    # Lean-proven Z3Z6 pair: doubling, rung never binds — expect margin >= 0
    rec = cell_margins((3, 6), "x^2 + y + y^3", "1 + x + y^2", "x", 4)
    print(json.dumps(rec, indent=1))
    ok = rec["worst_rung"] is not None and rec["worst_rung"]["margin"] >= 0
    print(f"CONTROL {'PASS' if ok else 'FAIL'} (expect worst margin >= 0 on the"
          " Lean-proven doubling pair)")
    sys.exit(0 if ok else 1)


def sweep(files: list[Path], out: Path, limit: int | None) -> None:
    cells = []
    seen = set()
    for p in files:
        for line in p.open():
            try:
                r = json.loads(line)
            except Exception:
                continue
            for a in r.get("axes", []):
                if a.get("csafe"):
                    key = (r["frame"], r["A"], r["B"], a["axis"])
                    if key not in seen:
                        seen.add(key)
                        cells.append((r, a))
    cells.sort(key=lambda ra: (ra[0]["d_base"], 2 * int(ra[0]["frame"][1]) *
                               int(ra[0]["frame"][3])))
    if limit:
        cells = cells[:limit]
    print(f"near-miss sweep over {len(cells)} C-safe-true cells -> {out}", flush=True)
    done = set()
    if out.exists():
        for line in out.open():
            try:
                r = json.loads(line)
                done.add((r["frame"], r["A"], r["B"], r["axis"]))
            except Exception:
                pass
    with out.open("a") as fh:
        for r, a in cells:
            fr = (int(r["frame"].split("xZ")[0][1:]), int(r["frame"].split("xZ")[1]))
            key = (r["frame"], r["A"], r["B"], a["axis"])
            if key in done:
                continue
            rec = cell_margins(fr, r["A"], r["B"], a["axis"], r["d_base"])
            rec["d_cover"] = a.get("d_cover", a.get("verdict"))
            fh.write(json.dumps(rec) + "\n")
            fh.flush()
            w = rec.get("worst_rung")
            print(f"  {key} d={r['d_base']} worst={w}", flush=True)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["control", "sweep"])
    ap.add_argument("--files", type=str, default=None)
    ap.add_argument("--out", type=str, default=str(CX_DIR / "nearmiss.jsonl"))
    ap.add_argument("--limit", type=int, default=None)
    args = ap.parse_args()
    if args.cmd == "control":
        control()
    else:
        files = ([Path(p) for p in args.files.split(",")] if args.files
                 else sorted(CX_DIR.glob("hunt_*.jsonl")))
        sweep(files, Path(args.out), args.limit)


if __name__ == "__main__":
    main()
