"""A11 CX — S2: light-b dangerous-rung slice probe (near-miss margins).

For an instance (H, A, B, axis) on the primal (Z) side, for each light base
Z-stabilizer b (0 < |b| < 2d, enumerated as 1-/2-/(3-)subsets of H_Z rows):

    slice-min(b) = min over ρ of |ρ + h| + |ρ + h'|,

with h = ∂₂ᶜ y_b, h' = ∂₂ⁿᶜ y_b at a seam-minimal preimage y_b, ρ RELAXED to
range over all nontrivial base Z-logical vectors (ker H_X^base, not in
rowspace H_Z^base).  Relaxation only widens the ρ pool vs the true τ-fiber
classes, so relaxed-slice-min <= true slice-min: a relaxed dip below 2d is a
NECESSARY precursor of a rung violation (then decided by d(cover) directly).

Also computes the punctured concentration bound m_out(b) = min nontrivial-ρ
weight OUTSIDE Σ(b) = supp(h) ∪ supp(h') (rung soundness bound:
slice(b) >= |b| + 2·m_out(b)), and the flux statistic (does every preimage of
b cross the seam?).

Subcommands:
    selftest             brute-force cross-check of both SAT encodings
    run --files ...      probe every C-safe-true cell in the hunt JSONLs
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from itertools import combinations
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
from bb_lab.sat_distance import _xor_chain, x_distance

from a9_lean_target_screen import cover_group, lift_poly
from a11_s4_dangerous_reduction import sheet_maps

CX_DIR = LAB_ROOT / "data" / "a11" / "cx"


# ---------------------------------------------------------------------------
# sheet split of the base boundary (V1 extraction, primal side)
# ---------------------------------------------------------------------------


def seam_split(ell: int, m: int, A: Poly, B: Poly, axis: str):
    """Return (chb, d2b, d2nc, d2cc): base ∂₂ (2n x n) and its non-crossing /
    crossing parts under the literal axis lift's fundamental domain."""
    Gb, Gc, S, Q = sheet_maps(ell, m, axis)
    nb = Gb.cardinality
    chb = bb_check_matrices(A, B)
    chc = bb_check_matrices(lift_poly(A, Gc), lift_poly(B, Gc))
    d2b = chb.H_Z.astype(np.uint8).T
    d2c_full = chc.H_Z.astype(np.uint8).T
    inv_q: dict[int, tuple[int, int]] = {}
    for s in (0, 1):
        for i, qi in enumerate(Q[s]):
            inv_q[int(qi)] = (s, i)
    d2nc = np.zeros((2 * nb, nb), dtype=np.uint8)
    d2cc = np.zeros((2 * nb, nb), dtype=np.uint8)
    for j in range(nb):
        col = d2c_full[:, S[0, j]]
        for qi in np.flatnonzero(col):
            s, i = inv_q[int(qi)]
            (d2nc if s == 0 else d2cc)[i, j] ^= 1
    assert ((d2nc ^ d2cc) == d2b).all(), "seam split does not sum to base d2"
    return Gb, chb, d2b, d2nc, d2cc


# ---------------------------------------------------------------------------
# SAT encodings over the nontrivial-logical set
# ---------------------------------------------------------------------------


def _base_logical_cnf(HXb: np.ndarray, LXb: np.ndarray):
    """CNF skeleton: ρ ∈ ker(HXb), ρ pairs oddly with >= 1 X-logical rep.
    Returns (cnf, pool, rho_vars)."""
    n = HXb.shape[1]
    pool = IDPool()
    rho = [pool.id() for _ in range(n)]
    cnf = CNF()
    for row in HXb:
        idx = np.flatnonzero(row)
        if idx.size == 0:
            continue
        out = _xor_chain((rho[i] for i in idx), pool, cnf)
        if out is not None:
            cnf.append([-out])
    outs = []
    for L in LXb:
        idx = np.flatnonzero(L)
        if idx.size == 0:
            continue
        out = _xor_chain((rho[i] for i in idx), pool, cnf)
        if out is not None:
            outs.append(out)
    if not outs:
        raise AssertionError("no logicals")
    cnf.append(outs)
    return cnf, pool, rho


def _solve(cnf: CNF, rho: list[int]) -> np.ndarray | None:
    solver = Cadical195(bootstrap_with=cnf.clauses)
    try:
        if not solver.solve():
            return None
        truth = {abs(l): l > 0 for l in solver.get_model()}
        return np.array([1 if truth.get(v, False) else 0 for v in rho], dtype=np.uint8)
    finally:
        solver.delete()


def slice_min_le(HXb: np.ndarray, LXb: np.ndarray, h: np.ndarray, hp: np.ndarray,
                 W: int) -> np.ndarray | None:
    """SAT: ∃ nontrivial base Z-logical ρ with |ρ+h| + |ρ+h'| <= W."""
    cnf, pool, rho = _base_logical_cnf(HXb, LXb)
    lits = []
    for i in range(len(rho)):
        lits.append(-rho[i] if h[i] else rho[i])
    for i in range(len(rho)):
        lits.append(-rho[i] if hp[i] else rho[i])
    if W < len(lits):
        cnf.extend(CardEnc.atmost(lits=lits, bound=W, vpool=pool,
                                  encoding=EncType.seqcounter).clauses)
    return _solve(cnf, rho)


def punctured_min_le(HXb: np.ndarray, LXb: np.ndarray, sigma: np.ndarray,
                     w: int) -> np.ndarray | None:
    """SAT: ∃ nontrivial base Z-logical ρ with |ρ restricted outside Σ| <= w."""
    cnf, pool, rho = _base_logical_cnf(HXb, LXb)
    lits = [rho[i] for i in range(len(rho)) if not sigma[i]]
    if w < len(lits):
        cnf.extend(CardEnc.atmost(lits=lits, bound=w, vpool=pool,
                                  encoding=EncType.seqcounter).clauses)
    return _solve(cnf, rho)


def slice_min(HXb, LXb, h, hp, cap: int) -> int | None:
    """Exact relaxed slice-min if <= cap else None.  Parity of the slice is
    |h + h'| = |b| mod 2, ladder step 2."""
    b_par = int((h ^ hp).sum() % 2)
    # slice weight parity == |b| mod 2; weight 0 impossible (would force b = 0)
    start = 1 if b_par else 2
    for W in range(start, cap + 1, 2):
        if slice_min_le(HXb, LXb, h, hp, W) is not None:
            return W
    return None


def punctured_min(HXb, LXb, sigma, cap: int) -> int | None:
    for w in range(0, cap + 1):
        if punctured_min_le(HXb, LXb, sigma, w) is not None:
            return w
    return None


# ---------------------------------------------------------------------------
# per-instance probe
# ---------------------------------------------------------------------------


def probe_instance(frame: str, a_s: str, b_s: str, axis: str,
                   d_base: int | None = None, max_subset: int = 2,
                   margin_extra: int = 2) -> dict:
    # frame label like "Z3xZ4"
    parts = frame.replace("Z", "").split("x")
    ell, m = int(parts[0]), int(parts[1])
    Gb0 = AbelianGroup((ell, m))
    A = Poly.from_string(a_s, Gb0)
    B = Poly.from_string(b_s, Gb0)
    Gb, chb, d2b, d2nc, d2cc = seam_split(ell, m, A, B, axis)
    nb = Gb.cardinality
    HXb = chb.H_X.astype(np.uint8)
    kerZb = nullspace_f2(chb.H_Z.astype(np.uint8))
    LXb = quotient_complement_basis(HXb, kerZb)
    if d_base is None:
        d_base = x_distance(chb, weight_upper_bound=12).distance
    d = d_base
    twod = 2 * d
    ker2 = nullspace_f2(d2b)                       # 2-chain kernel (cells)
    dimk = ker2.shape[0]
    # all kernel elements (dim is k/2 — tiny)
    if dimk <= 12:
        idx = np.arange(1 << dimk, dtype=np.uint64)
        coeff = ((idx[:, None] >> np.arange(dimk, dtype=np.uint64)[None, :]) & 1
                 ).astype(np.uint8)
        ker_all = (coeff @ ker2) % 2 if dimk else np.zeros((1, nb), np.uint8)
    else:
        ker_all = np.vstack([np.zeros((1, nb), np.uint8), ker2 % 2])

    out: dict = {"frame": frame, "A": a_s, "B": b_s, "axis": axis, "d": d}
    rows: list[dict] = []
    seen_b: set[bytes] = set()
    subsets = []
    for sz in range(1, max_subset + 1):
        subsets.extend(combinations(range(nb), sz))
    n_flux_forced = 0
    n_light = 0
    for sub in subsets:
        y0 = np.zeros(nb, dtype=np.uint8)
        for j in sub:
            y0[j] = 1
        b = (d2b @ y0) % 2
        wb = int(b.sum())
        if wb == 0 or wb >= twod:
            continue
        key = b.tobytes()
        if key in seen_b:
            continue
        seen_b.add(key)
        n_light += 1
        # seam-minimal preimage over the ker coset
        best = None
        for zeta in ker_all:
            y = y0 ^ zeta
            h = (d2cc @ y) % 2
            hp = (d2nc @ y) % 2
            c = int(h.sum() + hp.sum())
            if best is None or c < best[0]:
                best = (c, h, hp)
        cmin, h, hp = best
        flux_forced = all(
            ((d2cc @ (y0 ^ z)) % 2).any() for z in ker_all
        )
        n_flux_forced += flux_forced
        sigma = (h | hp).astype(np.uint8)
        m_out = punctured_min(HXb, LXb, sigma, d)     # cap d: rung needs < d-|b|/2
        cap = twod - 2 + margin_extra                 # measure margins a bit past 2d
        sm = slice_min(HXb, LXb, h, hp, cap)
        rows.append({
            "b_w": wb, "hh": cmin, "overlap_seam": int((h & hp).sum()),
            "flux_forced": bool(flux_forced),
            "m_out": m_out if m_out is not None else f">{d}",
            "slice_min": sm if sm is not None else f">{cap}",
            "margin": (sm - twod) if sm is not None else f">={cap + 1 - twod}",
        })
    margins = [r["margin"] for r in rows if isinstance(r["margin"], int)]
    out["n_light_b"] = n_light
    out["n_flux_forced"] = n_flux_forced
    out["min_margin"] = min(margins) if margins else None
    out["rung_dips"] = sum(1 for mg in margins if mg < 0)
    out["rows"] = rows
    return out


# ---------------------------------------------------------------------------
# selftest — brute-force cross-check on a small instance
# ---------------------------------------------------------------------------


def selftest() -> None:
    frame, a_s, b_s, axis = "Z3xZ6", "x^2 + y + y^3", "1 + x + y^2", "x"
    ell, m = 3, 6
    Gb0 = AbelianGroup((ell, m))
    A = Poly.from_string(a_s, Gb0)
    B = Poly.from_string(b_s, Gb0)
    Gb, chb, d2b, d2nc, d2cc = seam_split(ell, m, A, B, axis)
    nb = Gb.cardinality
    HXb = chb.H_X.astype(np.uint8)
    HZb = chb.H_Z.astype(np.uint8)
    kerZb = nullspace_f2(HZb)
    LXb = quotient_complement_basis(HXb, kerZb)
    kerX = nullspace_f2(HXb)
    # brute-force the nontrivial-logical set (dim ker HXb small here)
    dim = kerX.shape[0]
    assert dim <= 22, dim
    idx = np.arange(1 << dim, dtype=np.uint64)
    allv = []
    # rowspace HZb membership via dual parities
    for blk in range(0, 1 << dim, 1 << 14):
        sl = idx[blk: blk + (1 << 14)]
        coeff = ((sl[:, None] >> np.arange(dim, dtype=np.uint64)[None, :]) & 1
                 ).astype(np.uint8)
        vs = (coeff @ kerX) % 2
        nontriv = ((vs @ kerZb.T) % 2).any(axis=1)   # v in rowspace(HZb) iff dual·v=0
        allv.append(vs[nontriv])
    NT = np.vstack(allv)
    print(f"selftest: |nontrivial set| = {NT.shape[0]} (dim ker HX = {dim})")
    rng = np.random.default_rng(7)
    ok = True
    for trial in range(4):
        j1, j2 = rng.integers(0, nb, 2)
        y0 = np.zeros(nb, np.uint8)
        y0[j1] ^= 1
        y0[j2] ^= 1
        h = (d2cc @ y0) % 2
        hp = (d2nc @ y0) % 2
        # brute-force slice min
        w0 = ((NT ^ h[None, :]).sum(axis=1) + (NT ^ hp[None, :]).sum(axis=1)).min()
        sm = slice_min(HXb, LXb, h, hp, int(w0) + 2)
        # brute-force punctured min
        sigma = (h | hp).astype(bool)
        pm_true = (NT[:, ~sigma]).sum(axis=1).min()
        pm = punctured_min(HXb, LXb, sigma.astype(np.uint8), int(pm_true) + 2)
        okt = (sm == int(w0)) and (pm == int(pm_true))
        ok &= okt
        print(f"  trial {trial}: slice SAT {sm} vs brute {int(w0)}; "
              f"punctured SAT {pm} vs brute {int(pm_true)}  "
              f"[{'PASS' if okt else 'FAIL'}]")
    # doc-pair rung check: all slice margins should be >= 0 (d(cover)=8=2d)
    res = probe_instance("Z3xZ6", a_s, b_s, axis, d_base=4)
    print(f"  doc-pair probe: n_light_b={res['n_light_b']} "
          f"min_margin={res['min_margin']} rung_dips={res['rung_dips']} (expect >= 0, 0)")
    ok &= res["rung_dips"] == 0
    print(f"SELFTEST: {'ALL PASS' if ok else 'FAILURE'}")
    sys.exit(0 if ok else 1)


# ---------------------------------------------------------------------------
# run over the hunt stream's C-safe-true cells
# ---------------------------------------------------------------------------


def run(files: list[Path], out_path: Path, budget_sec: int, limit: int | None,
        max_subset: int) -> None:
    cells = []
    for p in files:
        for line in p.open():
            try:
                r = json.loads(line)
            except Exception:
                continue
            for a in r.get("axes", []):
                if a.get("csafe"):
                    cells.append((r["frame"], r["A"], r["B"], a["axis"],
                                  r["d_base"], a.get("verdict")))
    if limit:
        cells = cells[:limit]
    print(f"slice probe over {len(cells)} C-safe-true cells", flush=True)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    done = set()
    if out_path.exists():
        for line in out_path.open():
            try:
                r = json.loads(line)
                done.add((r["frame"], r["A"], r["B"], r["axis"]))
            except Exception:
                pass
    t0 = time.time()
    n_dip = 0
    with out_path.open("a") as fh:
        for i, (fr, a_s, b_s, axis, d, verdict) in enumerate(cells):
            if (fr, a_s, b_s, axis) in done:
                continue
            if time.time() - t0 > budget_sec:
                print("budget exhausted", flush=True)
                break
            try:
                res = probe_instance(fr, a_s, b_s, axis, d_base=d,
                                     max_subset=max_subset)
                res["hunt_verdict"] = verdict
            except Exception as e:
                res = {"frame": fr, "A": a_s, "B": b_s, "axis": axis,
                       "error": str(e)}
            fh.write(json.dumps(res) + "\n")
            fh.flush()
            if isinstance(res.get("rung_dips"), int) and res["rung_dips"] > 0:
                n_dip += 1
                print(f"  RELAXED RUNG DIP: {fr} {a_s} | {b_s} {axis} "
                      f"min_margin={res['min_margin']} (hunt verdict {verdict})",
                      flush=True)
            if (i + 1) % 20 == 0:
                print(f"  [{i+1}/{len(cells)}] {time.time()-t0:.0f}s dips={n_dip}",
                      flush=True)
    print(f"done: {n_dip} cells with relaxed rung dips", flush=True)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["selftest", "run"])
    ap.add_argument("--files", type=str, default=None)
    ap.add_argument("--out", type=str, default=str(CX_DIR / "slice.jsonl"))
    ap.add_argument("--budget-sec", type=int, default=1800)
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--max-subset", type=int, default=2)
    args = ap.parse_args()
    if args.cmd == "selftest":
        selftest()
    else:
        files = ([Path(p) for p in args.files.split(",")] if args.files
                 else sorted(CX_DIR.glob("hunt_*.jsonl")))
        run(files, Path(args.out), args.budget_sec, args.limit, args.max_subset)


if __name__ == "__main__":
    main()
