"""A11 CX — counterexample hunt for "C-safe implies literal-lift doubling".

C-safe for a cell (H, A, B, axis):
  1. k(cover) = k(base)                       (rank, cheap)
  2. tight witness                            (profile_pair semantics: some
     translate of a weight-d base Z-logical lifts diagonally to a nontrivial
     cover Z-logical)
  3. safe floor: every nonzero class of im p_* in H1(base) has base coset
     min >= 2*d(base)                         (SAT coset ladders)

A counterexample = C-safe TRUE and d(cover) < 2*d(base).

Hunt distribution (outside the screened corpus): weight-4/5 polynomial
pairs on small frames, plus weight-3 pairs at d(base) in {2,3} (the A9
stream only screened d >= 4), plus adversarial seam-heavy/spread modes.

Encoding-safety notes vs the existing a11_s3 helpers:
  * coset_min here ladders with step 1 whenever |A|+|B| is odd (mixed-parity
    cosets; a step-2 ladder can MISS the true minimum there).  Step 2 is only
    used when every H_Z row has even weight.
  * the ladder's lower bound `lo` is d(base) for safe classes (every nonzero
    im p_* class is a nontrivial base Z-logical class, so its coset min is
    >= d_Z = d_X = d by the BB transpose symmetry); jackpot verification
    re-runs everything from lo = 1.

Subcommands:
    control            validation ladder (documented Z3Z6 + hit3 values)
    hunt               the sampling hunt (JSONL, append-only, resumable)
    verify             full independent re-verification of one cell
    report             aggregate JSONL -> coverage/verdict tables

Usage examples:
    uv run python scripts/a11_cx_hunt.py control
    uv run python scripts/a11_cx_hunt.py hunt --tag small44 \
        --frames 3,3:3,4:4,4 --weights 4,4:4,3:3,4 --modes rand,heavyx,heavyy \
        --per-block 400 --budget-sec 4200
    uv run python scripts/a11_cx_hunt.py verify --frame 3,4 \
        --A "..." --B "..." --axis x
    uv run python scripts/a11_cx_hunt.py report
"""

from __future__ import annotations

import argparse
import itertools
import json
import sys
import time
from pathlib import Path

import numpy as np

LAB_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LAB_ROOT / "src"))
sys.path.insert(0, str(LAB_ROOT / "scripts"))

from bb_lab.checks import bb_check_matrices
from bb_lab.codeparams import code_params
from bb_lab.group import AbelianGroup
from bb_lab.linalg import nullspace_f2, rank_f2, quotient_complement_basis
from bb_lab.poly import Poly
from bb_lab.sat_distance import x_distance, find_logical_z, _solve_at_weight

from a9_lean_target_screen import blkdiag, cover_group, cover_maps, lift_poly
from a11_s3_diagnose import coset_min_le

CX_DIR = LAB_ROOT / "data" / "a11" / "cx"

RMAX = 8                # max rank(im p_*) for exhaustive safe-class ladders
DBASE_CAP = 12          # skip pairs with d(base) > this
COVER_LADDER_SKIP = 16  # skip the cover ladder when 2d exceeds this on big covers
BIG_COVER = 84          # ... and n_cover >= this


# ---------------------------------------------------------------------------
# F2 incremental span (pivot-indexed echelon rows) — fast repeated membership
# ---------------------------------------------------------------------------


class F2Span:
    __slots__ = ("piv",)

    def __init__(self) -> None:
        self.piv: dict[int, np.ndarray] = {}

    def reduce(self, v: np.ndarray) -> np.ndarray:
        v = (v & 1).astype(np.uint8, copy=True)
        while True:
            nz = np.flatnonzero(v)
            if nz.size == 0:
                return v
            p = int(nz[0])
            row = self.piv.get(p)
            if row is None:
                return v
            v ^= row

    def add(self, v: np.ndarray) -> bool:
        r = self.reduce(v)
        nz = np.flatnonzero(r)
        if nz.size == 0:
            return False
        self.piv[int(nz[0])] = r
        return True

    def contains(self, v: np.ndarray) -> bool:
        return not self.reduce(v).any()

    def copy(self) -> "F2Span":
        s = F2Span()
        s.piv = dict(self.piv)
        return s


def span_of(M: np.ndarray) -> F2Span:
    s = F2Span()
    for row in M:
        s.add(row)
    return s


# ---------------------------------------------------------------------------
# coset minimum (parity-safe ladder)
# ---------------------------------------------------------------------------


def coset_min_cx(rep: np.ndarray, dual: np.ndarray, cap: int, lo: int,
                 even_gen: bool) -> int | None:
    """Exact min weight in rep + rowspace(S) if <= cap, else None (>= cap+1).

    `dual` = nullspace(S).  `lo` must be a PROVEN lower bound on the coset
    min (pass 1 when unsure).  `even_gen` = all rows of S have even weight
    (then the coset has fixed parity and the ladder may step by 2)."""
    if not rep.any():
        return 0
    lo = max(lo, 1)
    if even_gen:
        par = int(rep.sum() % 2)
        start = lo if lo % 2 == par else lo + 1
        step = 2
    else:
        start, step = lo, 1
    for w in range(start, cap + 1, step):
        if coset_min_le(rep, dual, w) is not None:
            return w
    return None


# ---------------------------------------------------------------------------
# tight witness (profile_pair semantics, precomputed translate perms)
# ---------------------------------------------------------------------------

_PERM_CACHE: dict[tuple[int, int], list[np.ndarray]] = {}


def translate_perms(Gb: AbelianGroup) -> list[np.ndarray]:
    key = tuple(Gb.orders)
    if key not in _PERM_CACHE:
        ell, m = Gb.orders
        perms = []
        for g in Gb:
            p = np.array(
                [Gb.index(((h[0] + g[0]) % ell, (h[1] + g[1]) % m)) for h in Gb],
                dtype=np.int64,
            )
            perms.append(p)
        _PERM_CACHE[key] = perms
    return _PERM_CACHE[key]


def tight_witness_cx(Gb: AbelianGroup, ustar: np.ndarray, tau_blk: np.ndarray,
                     HXc: np.ndarray, spanZc: F2Span) -> bool:
    """Does some translate of the weight-d base Z-logical `ustar` lift
    diagonally to a nontrivial cover Z-logical?"""
    nb = Gb.cardinality
    T = blkdiag(tau_blk)
    for perm in translate_perms(Gb):
        tr = np.zeros_like(ustar)
        tr[perm] = ustar[:nb]
        tr[nb + perm] = ustar[nb:]
        tau_u = (T @ tr) % 2
        if not ((HXc @ tau_u) % 2).any() and not spanZc.contains(tau_u):
            return True
    return False


# ---------------------------------------------------------------------------
# per-pair evaluation
# ---------------------------------------------------------------------------


def eval_pair(Gb: AbelianGroup, A: Poly, B: Poly, mode: str,
              rmax: int = RMAX) -> dict:
    """Evaluate the C-safe pipeline on (A, B) and both axis lifts."""
    ell, m = Gb.orders
    t0 = time.time()
    rec: dict = {
        "frame": Gb.label(), "A": A.canonical_string(), "B": B.canonical_string(),
        "wA": A.weight(), "wB": B.weight(), "mode": mode,
    }
    chb = bb_check_matrices(A, B)
    pb = code_params(chb)
    rec["k"] = pb.k
    if pb.k <= 0:
        rec["stage"] = "k0"
        rec["t"] = round(time.time() - t0, 3)
        return rec
    try:
        resb = x_distance(chb, weight_upper_bound=DBASE_CAP)
    except RuntimeError:
        rec["stage"] = "dbase_over_cap"
        rec["t"] = round(time.time() - t0, 3)
        return rec
    d = resb.distance
    rec["d_base"] = d
    if d < 2:
        rec["stage"] = "d1"
        rec["t"] = round(time.time() - t0, 3)
        return rec

    HXb = chb.H_X.astype(np.uint8)
    HZb = chb.H_Z.astype(np.uint8)
    kerZb = nullspace_f2(HZb)          # = dual for rowspace(HZb) membership
    LXb = quotient_complement_basis(HXb, kerZb)
    wit, _ = _solve_at_weight(HXb, LXb, d)
    if wit is None:
        rec["stage"] = "ALARM_no_base_witness"   # should be impossible (d_Z = d_X)
        rec["t"] = round(time.time() - t0, 3)
        return rec
    wit = (wit & 1).astype(np.uint8)
    even_gen = (A.weight() + B.weight()) % 2 == 0
    spanZb = span_of(HZb)

    rec["stage"] = "axes"
    rec["axes"] = []
    for axis in ("x", "y"):
        ta = time.time()
        arec: dict = {"axis": axis}
        Gc = cover_group(ell, m, axis)
        chc = bb_check_matrices(lift_poly(A, Gc), lift_poly(B, Gc))
        pc = code_params(chc)
        arec["k_cover"] = pc.k
        if pc.k != pb.k:
            arec["verdict"] = "k_drift"
            arec["t"] = round(time.time() - ta, 3)
            rec["axes"].append(arec)
            continue
        HXc = chc.H_X.astype(np.uint8)
        HZc = chc.H_Z.astype(np.uint8)
        p_blk, tau_blk, _sig, _deck = cover_maps(Gb, Gc, axis)
        spanZc = span_of(HZc)
        tw = tight_witness_cx(Gb, wit, tau_blk, HXc, spanZc)
        arec["tight_witness"] = tw
        if not tw:
            arec["verdict"] = "no_tight_witness"
            arec["t"] = round(time.time() - ta, 3)
            rec["axes"].append(arec)
            continue
        # safe classes: im p_* mod rowspace(HZb)
        LZc = find_logical_z(chc)
        P = blkdiag(p_blk)
        spanQ = spanZb.copy()
        reps: list[np.ndarray] = []
        for i in range(LZc.shape[0]):
            img = (P @ LZc[i]) % 2
            if spanQ.add(img):
                reps.append(img.astype(np.uint8))
        r = len(reps)
        arec["rank_p_star"] = r
        cap = 2 * d - 1
        if r > rmax:
            arec["verdict"] = "safe_r_too_big"
            arec["t"] = round(time.time() - ta, 3)
            rec["axes"].append(arec)
            continue
        floor_ok = True
        fail_min = None
        for mask in range(1, 1 << r):
            combo = np.zeros(2 * Gb.cardinality, dtype=np.uint8)
            for i in range(r):
                if (mask >> i) & 1:
                    combo ^= reps[i]
            mmin = coset_min_cx(combo, kerZb, cap, d, even_gen)
            if mmin is not None:
                floor_ok = False
                fail_min = mmin
                break
        if not floor_ok:
            arec["verdict"] = "safe_floor_fail"
            arec["fail_min"] = fail_min
            arec["t"] = round(time.time() - ta, 3)
            rec["axes"].append(arec)
            continue
        # C-safe TRUE -> the moment of truth
        arec["csafe"] = True
        if 2 * d > COVER_LADDER_SKIP and chc.num_qubits >= BIG_COVER:
            arec["verdict"] = "CSAFE_TRUE_unladdered"
            arec["t"] = round(time.time() - ta, 3)
            rec["axes"].append(arec)
            continue
        resc = x_distance(chc, weight_upper_bound=2 * d)
        arec["d_cover"] = resc.distance
        if resc.distance == 2 * d:
            arec["verdict"] = "CSAFE_DOUBLES"
        else:
            arec["verdict"] = "COUNTEREXAMPLE"
            arec["witness"] = [int(b) for b in resc.witness]
        arec["t"] = round(time.time() - ta, 3)
        rec["axes"].append(arec)
    rec["t"] = round(time.time() - t0, 3)
    return rec


# ---------------------------------------------------------------------------
# sampling
# ---------------------------------------------------------------------------


def sample_poly(Gb: AbelianGroup, w: int, rng: np.random.Generator,
                mode: str) -> Poly:
    ell, m = Gb.orders
    supp: set[tuple[int, int]] = set()
    if mode.startswith("spread"):
        axis = 0 if mode == "spreadx" else 1
        order = ell if axis == 0 else m
        exps = list(rng.permutation(order))
        tries = 0
        while len(supp) < w and tries < 200:
            e = int(exps[len(supp) % order])
            other = int(rng.integers(0, m if axis == 0 else ell))
            g = (e, other) if axis == 0 else (other, e)
            supp.add(g)
            tries += 1
    else:
        tries = 0
        while len(supp) < w and tries < 500:
            if mode == "heavyx":
                gx = int(rng.integers(ell // 2, ell)) if rng.random() < 0.75 \
                    else int(rng.integers(0, ell))
                gy = int(rng.integers(0, m))
            elif mode == "heavyy":
                gx = int(rng.integers(0, ell))
                gy = int(rng.integers(m // 2, m)) if rng.random() < 0.75 \
                    else int(rng.integers(0, m))
            else:  # rand
                gx = int(rng.integers(0, ell))
                gy = int(rng.integers(0, m))
            supp.add((gx, gy))
            tries += 1
    if len(supp) < w:
        # tiny group / heavy constraints: pad uniformly
        elems = [tuple(g) for g in Gb]
        rng.shuffle(elems)
        for g in elems:
            supp.add(g)
            if len(supp) == w:
                break
    return Poly.from_support(supp, Gb)


# ---------------------------------------------------------------------------
# the hunt loop
# ---------------------------------------------------------------------------


def load_seen(out: Path) -> set[tuple[str, str, str]]:
    seen = set()
    if out.exists():
        for line in out.open():
            try:
                r = json.loads(line)
                seen.add((r["frame"], r["A"], r["B"]))
            except Exception:
                continue
    return seen


def hunt(args: argparse.Namespace) -> None:
    frames = [tuple(int(t) for t in f.split(",")) for f in args.frames.split(":")]
    weights = [tuple(int(t) for t in wp.split(",")) for wp in args.weights.split(":")]
    modes = args.modes.split(",")
    out = Path(args.out) if args.out else CX_DIR / f"hunt_{args.tag}.jsonl"
    out.parent.mkdir(parents=True, exist_ok=True)
    seen = load_seen(out)
    print(f"[{args.tag}] hunt: frames={frames} weights={weights} modes={modes} "
          f"per-block={args.per_block} budget={args.budget_sec}s "
          f"resume-skip={len(seen)}", flush=True)
    rng = np.random.default_rng(args.seed)
    t0 = time.time()
    blocks = [(fr, wp, mo) for fr in frames for wp in weights for mo in modes]
    counters: dict[str, int] = {}
    n_written = n_csafe = 0
    stop = False
    with out.open("a") as fh:
        # breadth-first: chunks of `chunk` samples per block, repeated passes
        chunk = max(10, args.per_block // 10)
        done_per_block = {b: 0 for b in blocks}
        for _pass in itertools.count():
            if stop or all(done_per_block[b] >= args.per_block for b in blocks):
                break
            for b in blocks:
                if stop:
                    break
                (fr, wp, mo) = b
                if done_per_block[b] >= args.per_block:
                    continue
                Gb = AbelianGroup(fr)
                for _ in range(min(chunk, args.per_block - done_per_block[b])):
                    if time.time() - t0 > args.budget_sec:
                        stop = True
                        break
                    A = sample_poly(Gb, wp[0], rng, mo)
                    B = sample_poly(Gb, wp[1], rng, mo)
                    done_per_block[b] += 1
                    key = (Gb.label(), A.canonical_string(), B.canonical_string())
                    if key in seen:
                        continue
                    seen.add(key)
                    try:
                        rec = eval_pair(Gb, A, B, mo)
                    except Exception as e:
                        rec = {"frame": Gb.label(), "A": key[1], "B": key[2],
                               "mode": mo, "stage": f"error: {e}"}
                    fh.write(json.dumps(rec) + "\n")
                    fh.flush()
                    n_written += 1
                    counters[rec.get("stage", "?")] = counters.get(rec.get("stage", "?"), 0) + 1
                    for arec in rec.get("axes", []):
                        v = arec.get("verdict", "?")
                        counters[v] = counters.get(v, 0) + 1
                        if arec.get("csafe"):
                            n_csafe += 1
                        if v == "COUNTEREXAMPLE":
                            print(f"\n!!! COUNTEREXAMPLE CANDIDATE !!!\n{json.dumps(rec)}\n",
                                  flush=True)
                if done_per_block[b] % (chunk * 2) == 0 or stop:
                    el = time.time() - t0
                    print(f"[{args.tag}] {el:6.0f}s pass={_pass} wrote={n_written} "
                          f"csafe={n_csafe} {counters}", flush=True)
    print(f"[{args.tag}] DONE {time.time()-t0:.0f}s wrote={n_written} "
          f"csafe-true={n_csafe} counters={counters}", flush=True)


# ---------------------------------------------------------------------------
# controls (validation ladder — run before quoting any hunt output)
# ---------------------------------------------------------------------------


def control() -> None:
    import collections
    print("== control 1: Z3Z6 doc pair (A=x^2+y+y^3, B=1+x+y^2, axis x) ==", flush=True)
    Gb = AbelianGroup((3, 6))
    A = Poly.from_string("x^2 + y + y^3", Gb)
    B = Poly.from_string("1 + x + y^2", Gb)
    chb = bb_check_matrices(A, B)
    pb = code_params(chb)
    resb = x_distance(chb, weight_upper_bound=8)
    print(f"  k(base) = {pb.k} (expect 4), d(base) = {resb.distance} (expect 4)")
    ok1 = pb.k == 4 and resb.distance == 4
    rec = eval_pair(Gb, A, B, "control")
    ax = {a["axis"]: a for a in rec["axes"]}
    print(f"  eval_pair: d={rec['d_base']}, x-axis verdict = {ax['x'].get('verdict')} "
          f"d_cover = {ax['x'].get('d_cover')} (expect CSAFE_DOUBLES, 8)")
    ok2 = ax["x"].get("verdict") == "CSAFE_DOUBLES" and ax["x"].get("d_cover") == 8

    # safe-floor histogram with lo=1 (full ladder, no shortcut) — expect all >= 8
    kerZb = nullspace_f2(chb.H_Z.astype(np.uint8))
    Gc = cover_group(3, 6, "x")
    chc = bb_check_matrices(lift_poly(A, Gc), lift_poly(B, Gc))
    p_blk, _t, _s, _d = cover_maps(Gb, Gc, "x")
    LZc = find_logical_z(chc)
    P = blkdiag(p_blk)
    spanQ = span_of(chb.H_Z.astype(np.uint8))
    reps = [img.astype(np.uint8) for i in range(LZc.shape[0])
            if spanQ.add(img := (P @ LZc[i]) % 2)]
    minima = []
    for mask in range(1, 1 << len(reps)):
        combo = np.zeros(2 * Gb.cardinality, dtype=np.uint8)
        for i in range(len(reps)):
            if (mask >> i) & 1:
                combo ^= reps[i]
        minima.append(coset_min_cx(combo, kerZb, 7, 1, True))
    hist = collections.Counter(">=8" if v is None else str(v) for v in minima)
    print(f"  safe minima (cap 7, lo=1): {dict(hist)} over {len(minima)} classes "
          f"(expect all >=8, 3 classes)")
    ok3 = all(v is None for v in minima) and len(minima) == 3

    print("== control 2: hit3 stored Z6xZ6 (A=y^3+x+x^2, B=y+x*y^2+x^2, axis x) ==", flush=True)
    G6 = AbelianGroup((6, 6))
    A6 = Poly.from_string("y^3 + x + x^2", G6)
    B6 = Poly.from_string("y + x*y^2 + x^2", G6)
    ch6 = bb_check_matrices(A6, B6)
    ker6 = nullspace_f2(ch6.H_Z.astype(np.uint8))
    Gc6 = cover_group(6, 6, "x")
    chc6 = bb_check_matrices(lift_poly(A6, Gc6), lift_poly(B6, Gc6))
    p6, _t6, _s6, _d6 = cover_maps(G6, Gc6, "x")
    LZ6 = find_logical_z(chc6)
    P6 = blkdiag(p6)
    spanQ6 = span_of(ch6.H_Z.astype(np.uint8))
    reps6 = [img.astype(np.uint8) for i in range(LZ6.shape[0])
             if spanQ6.add(img := (P6 @ LZ6[i]) % 2)]
    t0 = time.time()
    minima6 = []
    for mask in range(1, 1 << len(reps6)):
        combo = np.zeros(72, dtype=np.uint8)
        for i in range(len(reps6)):
            if (mask >> i) & 1:
                combo ^= reps6[i]
        minima6.append(coset_min_cx(combo, ker6, 11, 6, True))  # lo = d = 6
    hist6 = collections.Counter(">=12" if v is None else str(v) for v in minima6)
    print(f"  hit3:stored:x safe minima: {dict(sorted(hist6.items()))} "
          f"({time.time()-t0:.1f}s) (expect {{6:12, 8:45, >=12:6}})")
    ok4 = hist6.get("6", 0) == 12 and hist6.get("8", 0) == 45 and hist6.get(">=12", 0) == 6

    print("== control 3: mixed-parity coset ladder (step-1 path) ==", flush=True)
    # tiny synthetic check: S = single odd-weight row; coset of rep=e0
    S = np.array([[1, 1, 1, 0, 0]], dtype=np.uint8)
    dual = nullspace_f2(S)
    rep = np.array([1, 0, 0, 0, 0], dtype=np.uint8)
    m1 = coset_min_cx(rep, dual, 4, 1, False)
    # coset = {e0, e0+row} = {10000 (w1), 01100+... (w2? 1+11100=01100 w2)}
    ok5 = m1 == 1
    rep2 = np.array([0, 1, 1, 1, 1], dtype=np.uint8)   # w4; +row -> 10011 w... 0,1,1,1,1 ^ 1,1,1,0,0 = 1,0,0,1,1 w3
    m2 = coset_min_cx(rep2, dual, 4, 1, False)
    ok5 = ok5 and m2 == 3
    print(f"  synthetic minima: {m1} (expect 1), {m2} (expect 3)")

    allok = ok1 and ok2 and ok3 and ok4 and ok5
    print(f"\nCONTROLS: {'ALL PASS' if allok else 'FAILURE'} "
          f"({ok1=} {ok2=} {ok3=} {ok4=} {ok5=})", flush=True)
    sys.exit(0 if allok else 1)


# ---------------------------------------------------------------------------
# independent verification of a candidate counterexample
# ---------------------------------------------------------------------------


def verify(frame: str, a_s: str, b_s: str, axis: str, out_json: Path | None) -> dict:
    import collections
    ell, m = (int(t) for t in frame.split(","))
    Gb = AbelianGroup((ell, m))
    A, B = Poly.from_string(a_s, Gb), Poly.from_string(b_s, Gb)
    Gc = cover_group(ell, m, axis)
    chb = bb_check_matrices(A, B)
    chc = bb_check_matrices(lift_poly(A, Gc), lift_poly(B, Gc))
    HXb, HZb = chb.H_X.astype(np.uint8), chb.H_Z.astype(np.uint8)
    HXc, HZc = chc.H_X.astype(np.uint8), chc.H_Z.astype(np.uint8)
    rep: dict = {"frame": frame, "A": a_s, "B": b_s, "axis": axis}

    # k from scratch
    kb = chb.num_qubits - rank_f2(HXb) - rank_f2(HZb)
    kc = chc.num_qubits - rank_f2(HXc) - rank_f2(HZc)
    rep["k_base"], rep["k_cover"] = kb, kc

    # distances from scratch, full ladders from weight 1
    resb = x_distance(chb, weight_upper_bound=chb.num_qubits)
    d = resb.distance
    rep["d_base"] = d
    resc = x_distance(chc, weight_upper_bound=2 * d)
    rep["d_cover"] = resc.distance

    # cover witness verified in pure numpy
    v = resc.witness.astype(np.uint8)
    rep["witness_weight"] = int(v.sum())
    rep["witness_in_ker_HZc"] = not ((HZc @ v) % 2).any()
    r0 = rank_f2(HXc)
    rep["witness_notin_rowspace_HXc"] = rank_f2(np.vstack([HXc, v[None, :]])) > r0
    rep["witness"] = [int(x) for x in v]

    # tight witness + safe floor from scratch (lo = 1 ladders, full histogram)
    kerZb = nullspace_f2(HZb)
    LXb = quotient_complement_basis(HXb, kerZb)
    wit, _ = _solve_at_weight(HXb, LXb, d)
    p_blk, tau_blk, _s, _dk = cover_maps(Gb, Gc, axis)
    spanZc = span_of(HZc)
    rep["tight_witness"] = bool(
        wit is not None and tight_witness_cx(Gb, (wit & 1).astype(np.uint8),
                                             tau_blk, HXc, spanZc))
    LZc = find_logical_z(chc)
    P = blkdiag(p_blk)
    spanQ = span_of(HZb)
    reps_l = [img.astype(np.uint8) for i in range(LZc.shape[0])
              if spanQ.add(img := (P @ LZc[i]) % 2)]
    even_gen = (A.weight() + B.weight()) % 2 == 0
    minima = []
    for mask in range(1, 1 << len(reps_l)):
        combo = np.zeros(2 * Gb.cardinality, dtype=np.uint8)
        for i in range(len(reps_l)):
            if (mask >> i) & 1:
                combo ^= reps_l[i]
        minima.append(coset_min_cx(combo, kerZb, 2 * d - 1, 1, even_gen))
    hist = collections.Counter(f">={2*d}" if v_ is None else str(v_) for v_ in minima)
    rep["safe_minima_hist"] = dict(sorted(hist.items()))
    rep["safe_floor_ok"] = all(v_ is None for v_ in minima)
    rep["csafe"] = bool(rep["k_cover"] == rep["k_base"] and rep["tight_witness"]
                        and rep["safe_floor_ok"])
    rep["is_counterexample"] = bool(rep["csafe"] and rep["d_cover"] < 2 * d)
    print(json.dumps(rep, indent=1))
    if out_json:
        out_json.parent.mkdir(parents=True, exist_ok=True)
        out_json.write_text(json.dumps(rep, indent=1))
    return rep


# ---------------------------------------------------------------------------
# report aggregation
# ---------------------------------------------------------------------------


def report(paths: list[Path]) -> None:
    import collections
    rows = []
    for p in paths:
        for line in p.open():
            try:
                rows.append(json.loads(line))
            except Exception:
                continue
    by = collections.defaultdict(lambda: collections.Counter())
    csafe_cells = []
    for r in rows:
        key = (r.get("frame"), f"{r.get('wA','?')}+{r.get('wB','?')}")
        st = r.get("stage", "?")
        by[key]["pairs"] += 1
        if st != "axes":
            by[key][st] += 1
            continue
        for a in r.get("axes", []):
            v = a.get("verdict", "?")
            by[key][v] += 1
            if a.get("csafe"):
                csafe_cells.append((r, a))
    print(f"{len(rows)} pairs total across {len(paths)} files")
    hdr = ["pairs", "k0", "dbase_over_cap", "d1", "k_drift", "no_tight_witness",
           "safe_floor_fail", "safe_r_too_big", "CSAFE_DOUBLES",
           "CSAFE_TRUE_unladdered", "COUNTEREXAMPLE"]
    print(f"{'frame':8} {'wA+wB':6} " + " ".join(f"{h:>16}" for h in hdr))
    for key in sorted(by):
        c = by[key]
        print(f"{key[0]:8} {key[1]:6} " + " ".join(f"{c.get(h,0):>16}" for h in hdr))
    n_cx = sum(1 for _, a in csafe_cells if a.get("verdict") == "COUNTEREXAMPLE")
    print(f"\nC-safe-true cells: {len(csafe_cells)}; counterexamples: {n_cx}")
    for r, a in csafe_cells:
        if a.get("verdict") == "COUNTEREXAMPLE":
            print("  CX:", r["frame"], r["A"], "|", r["B"], a["axis"],
                  "d", r["d_base"], "->", a["d_cover"])


# ---------------------------------------------------------------------------


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["control", "hunt", "verify", "report"])
    ap.add_argument("--tag", type=str, default="run")
    ap.add_argument("--frames", type=str, default="3,3:3,4")
    ap.add_argument("--weights", type=str, default="4,4")
    ap.add_argument("--modes", type=str, default="rand")
    ap.add_argument("--per-block", type=int, default=300)
    ap.add_argument("--budget-sec", type=int, default=3600)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--out", type=str, default=None)
    ap.add_argument("--frame", type=str)
    ap.add_argument("--A", type=str)
    ap.add_argument("--B", type=str)
    ap.add_argument("--axis", type=str, default="x")
    ap.add_argument("--files", type=str, default=None,
                    help="comma-separated JSONL paths for report")
    args = ap.parse_args()
    if args.cmd == "control":
        control()
    elif args.cmd == "hunt":
        hunt(args)
    elif args.cmd == "verify":
        out = CX_DIR / f"verify_{args.frame.replace(',', 'x')}_{args.axis}.json"
        verify(args.frame, args.A, args.B, args.axis, out)
    else:
        paths = ([Path(p) for p in args.files.split(",")] if args.files
                 else sorted(CX_DIR.glob("hunt_*.jsonl")))
        report(paths)


if __name__ == "__main__":
    main()
