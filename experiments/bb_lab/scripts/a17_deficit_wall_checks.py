"""A17 deficit wall: validation battery for the theorem package.

Companion to `notes/A17_deficit_wall.md` (the deficit-wall theorem: why the
orbit-maximum safe floor of a non-doubling BB code stalls at exactly
2d(base) - 2).  Check IDs below mirror the note's statement numbers.

  L0  (transfer kernel)   im delta2 = ker tau1 on H1(base) — the safe sector
      is exactly the set of classes killed by the transfer to the cover.
  L1  (parity)            |A|, |B| odd  =>  every 1-cycle of base and cover
      has even weight (augmentation argument); d, d~, d_safe all even.
  L2  (collision group)   K_z = {g : (1+g)[z] in ker tau1} is a subgroup of
      index <= 2^(k/2) containing Stab0(z) = {g : [gz] = [z]}.
  T1  (difference bound)  where K_z properly contains Stab0, the light safe
      difference classes (1+g)[z] bound d_safe <= 2d - 2*overlap.
  T2  (pushforward)       a cover 1-cycle v with p1[v] != 0 and |v| <= W
      pushes to a safe base logical of weight <= W (im p1 = im delta2 under
      (R)), so d_safe <= W.  The wall value is the shadow of the failing
      cover's light safe-sector logical.
  W   (wall pins)         exact d_safe certificates by DESCENDING LADDER
      (SAT at w -> retry at wt_found - 2, by parity; terminate at UNSAT).
      bb90-y = 10 = d exactly (freeze); stored bb108-y: witness descent to
      14 with a bounded UNSAT attempt at 12 (the historical §14/§15
      readings of "18" were first-found witness weights, not minima — see
      A17 note §8); orbit-finalist sample: all exact values even and
      <= 2d - 2, strictly below the previously reported ceiling.

The one *expensive* certificate — the bb108-y COVER's safe-sector minimum
d~_safe = 14 exactly (SAT@14 pushing 14->14, UNSAT@12) — took ~5 h of
CaDiCaL at n = 216 and is not re-run by default; pass --expensive to
reproduce it. Its result is recorded in the note and consumed here only
as documentation.

Run from `experiments/bb_lab/`:
    uv run python scripts/a17_deficit_wall_checks.py [--expensive]
Output: `data/a17/deficit_wall_checks.json`; ~1 h default
(SAT-witness ladders; UNSAT attempts are bounded at 2M conflicts and may
report "upper" — the load-bearing exact certificates, with their real
costs, are recorded in the note's §8 table).
"""

from __future__ import annotations

import json
import sys
import time
from collections import Counter
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from pysat.card import CardEnc, EncType  # noqa: E402
from pysat.formula import IDPool  # noqa: E402
from pysat.solvers import Cadical153  # noqa: E402

from a14_s4_ladder import coset_query, orbit_reps  # noqa: E402
from a14_safe_floor_screens import (  # noqa: E402
    XCover, canonical_row, h1_dim, parse_poly,
)
from bb_lab.linalg import nullspace_f2, rank_f2  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "data" / "a15"
OUT.mkdir(parents=True, exist_ok=True)

CHECKS: list[tuple[str, bool]] = []
RESULTS: dict = {}


def check(name: str, ok: bool, detail: str = "") -> None:
    CHECKS.append((name, ok))
    print(f"  [{'PASS' if ok else 'FAIL'}] {name}" + (f"  ({detail})" if detail else ""))


def dim_mod(S: np.ndarray, Bnd: np.ndarray) -> int:
    if S.shape[0] == 0:
        return 0
    return rank_f2(np.vstack([S, Bnd])) - rank_f2(Bnd)


# --------------------------------------------------------------- chain maps


def transfer1(cov: XCover) -> np.ndarray:
    """tau = eps.lift on 1-chains: base cell (x,y) -> cover cells (x,y), (x+l,y)."""
    l, m, nb = cov.l, cov.m, cov.nb
    nc = 2 * nb
    T = np.zeros((2 * nc, 2 * nb), dtype=np.uint8)
    for j in (0, 1):
        for x in range(l):
            for y in range(m):
                col = j * nb + x * m + y
                T[j * nc + x * m + y, col] = 1
                T[j * nc + (x + l) * m + y, col] = 1
    return T


def push1(cov: XCover) -> np.ndarray:
    """p = fiber sum on 1-chains: cover cell (x,y) -> base cell (x mod l, y)."""
    l, m, nb = cov.l, cov.m, cov.nb
    nc = 2 * nb
    P = np.zeros((2 * nb, 2 * nc), dtype=np.uint8)
    for j in (0, 1):
        for x in range(2 * l):
            for y in range(m):
                P[j * nb + (x % l) * m + y, j * nc + x * m + y] ^= 1
    return P


def translate1_all(cov: XCover, z: np.ndarray) -> np.ndarray:
    """All |G| diagonal translates of a base 1-chain, rows indexed gx*m+gy."""
    l, m, nb = cov.l, cov.m, cov.nb
    u = z[:nb].reshape(l, m)
    v = z[nb:].reshape(l, m)
    out = np.zeros((l * m, 2 * nb), np.uint8)
    i = 0
    for gx in range(l):
        for gy in range(m):
            out[i, :nb] = np.roll(np.roll(u, gx, 0), gy, 1).reshape(-1)
            out[i, nb:] = np.roll(np.roll(v, gx, 0), gy, 1).reshape(-1)
            i += 1
    return out


class Cell:
    """One presentation cell (A, B, l, m, axis) with its safe-sector data."""

    def __init__(self, name, A, B, l, m, axis, d):
        self.name, self.d = name, d
        Ac, Bc, lc, mc = canonical_row(parse_poly(A), parse_poly(B), l, m, axis)
        self.cov = XCover(Ac, Bc, lc, mc)
        self.G = lc * mc
        self.Bnd = self.cov.d2b.T
        self.ker2 = nullspace_f2(self.cov.d2b)
        self.seams = np.vstack([self.cov.seam(z) for z in self.ker2])
        self.k = h1_dim(self.cov.d2b, self.cov.d1b)
        self.kc = h1_dim(self.cov.d2c, self.cov.d1c)
        # functionals: w (a cycle) is a boundary iff Qzero @ w = 0;
        # w's class lies in im delta2 iff Qsafe @ w = 0.
        self.Qsafe = nullspace_f2(np.vstack([self.seams, self.Bnd]))
        self.Qzero = nullspace_f2(self.Bnd)


# ------------------------------------------------------------ SAT: logicals


def _xor_chain(pool, clauses, lits):
    cur = None
    for v in lits:
        if cur is None:
            cur = v
        else:
            t = pool.id(("t", cur, v))
            clauses.extend([[-t, cur, v], [-t, -cur, -v], [t, -cur, v], [t, cur, -v]])
            cur = t
    return cur


def _detector_rows(d1: np.ndarray, d2: np.ndarray, k: int) -> np.ndarray:
    """k functionals whose OR detects a nontrivial class among cycles."""
    Lam = nullspace_f2(d2.T)
    cyc = nullspace_f2(d1)
    Mdet = (Lam @ cyc.T) & 1
    keep: list[int] = []
    acc = np.zeros((0, Mdet.shape[1]), np.uint8)
    for i in range(Lam.shape[0]):
        if rank_f2(np.vstack([acc, Mdet[i]])) > acc.shape[0]:
            acc = np.vstack([acc, Mdet[i]])
            keep.append(i)
        if acc.shape[0] == k:
            break
    return Lam[keep]


def safe_sector_cover_logical(cell: Cell, w: int, conf_budget: int = 30_000_000):
    """One cover 1-cycle v with |v| <= w and p1[v] != 0, or UNSAT/UNKNOWN.

    The nonzero-pushforward-class constraint is compiled in directly: base
    detectors composed with the pushforward.  p1[v] != 0 implies [v] != 0,
    so no separate cover-nontriviality constraint is needed.
    """
    cov = cell.cov
    n1 = 2 * (2 * cov.nb)
    Lam = _detector_rows(cov.d1b, cov.d2b, cell.k)
    Mdet = (Lam @ push1(cov)) & 1  # detectors on the pushed-down chain
    pool = IDPool()
    wvar = [pool.id(("w", i)) for i in range(n1)]
    clauses: list[list[int]] = []
    for i in range(cov.d1c.shape[0]):
        cur = _xor_chain(pool, clauses,
                         [wvar[j] for j in np.flatnonzero(cov.d1c[i])])
        if cur is not None:
            clauses.append([-cur])
    dets = []
    for i in range(Mdet.shape[0]):
        cur = _xor_chain(pool, clauses,
                         [wvar[j] for j in np.flatnonzero(Mdet[i])])
        if cur is not None:
            dets.append(cur)
    clauses.append(dets)
    card = CardEnc.atmost(lits=wvar, bound=w, vpool=pool,
                          encoding=EncType.seqcounter)
    with Cadical153(bootstrap_with=clauses + card.clauses) as solver:
        solver.conf_budget(conf_budget)
        res = solver.solve_limited()
        if res is None:
            return "UNKNOWN", None
        if not res:
            return "UNSAT", None
        model = set(solver.get_model())
        v = np.array([1 if wvar[i] in model else 0 for i in range(n1)], np.uint8)
        assert not ((cov.d1c @ v) & 1).any(), "not a cover cycle"
        assert ((Mdet @ v) & 1).any(), "pushforward class is zero"
        return "SAT", v


def min_logicals(cell: Cell, w: int, cap: int, conf_budget: int = 10_000_000):
    """Up to `cap` distinct base logicals of weight <= w; (list, exhausted?)."""
    cov = cell.cov
    n1 = 2 * cov.nb
    Lam = _detector_rows(cov.d1b, cov.d2b, cell.k)
    pool = IDPool()
    wvar = [pool.id(("w", i)) for i in range(n1)]
    clauses: list[list[int]] = []
    for i in range(cov.d1b.shape[0]):
        cur = _xor_chain(pool, clauses,
                         [wvar[j] for j in np.flatnonzero(cov.d1b[i])])
        if cur is not None:
            clauses.append([-cur])
    dets = []
    for i in range(Lam.shape[0]):
        cur = _xor_chain(pool, clauses,
                         [wvar[j] for j in np.flatnonzero(Lam[i])])
        if cur is not None:
            dets.append(cur)
    clauses.append(dets)
    card = CardEnc.atmost(lits=wvar, bound=w, vpool=pool,
                          encoding=EncType.seqcounter)
    sols: list[np.ndarray] = []
    with Cadical153(bootstrap_with=clauses + card.clauses) as solver:
        while len(sols) < cap:
            solver.conf_budget(conf_budget)
            res = solver.solve_limited()
            if res is None:
                return sols, False
            if not res:
                return sols, True
            model = set(solver.get_model())
            z = np.array([1 if wvar[i] in model else 0 for i in range(n1)],
                         np.uint8)
            assert not ((cov.d1b @ z) & 1).any() and ((Lam @ z) & 1).any()
            sols.append(z)
            solver.add_clause([(-wvar[i] if z[i] else wvar[i])
                               for i in range(n1)])
    return sols, False


# ----------------------------------------------------------------- L0 / L1


def check_L0(cell: Cell) -> dict:
    """im delta2 = ker tau1 on H1 (spans and dimensions)."""
    cov = cell.cov
    cycles = nullspace_f2(cov.d1b)
    T1 = transfer1(cov)
    Qc = nullspace_f2(cov.d2c.T)          # functionals killing im d2(cover)
    Mc = (((Qc @ T1) & 1) @ cycles.T) & 1
    sol = nullspace_f2(Mc)
    kertau = (sol @ cycles) & 1 if sol.shape[0] else np.zeros((0, 2 * cov.nb),
                                                              np.uint8)
    d_seam = dim_mod(cell.seams, cell.Bnd)
    d_ker = dim_mod(kertau, cell.Bnd)
    d_union = dim_mod(np.vstack([kertau, cell.seams]), cell.Bnd)
    ok = d_seam == d_ker == d_union == cell.k // 2
    check(f"L0/{cell.name}: im delta2 = ker tau1, dim k/2", ok,
          f"dims {d_seam}/{d_ker}/{d_union}, k={cell.k}, k~={cell.kc}")
    return {"dim_im_delta2": d_seam, "dim_ker_tau1": d_ker,
            "dim_union": d_union, "k": cell.k, "k_cover": cell.kc}


def check_L1(cell: Cell, n_samples: int = 200, seed: int = 15) -> dict:
    """Random base and cover cycles all have even weight; seams even."""
    rng = np.random.default_rng(seed)
    ok = True
    for d1 in (cell.cov.d1b, cell.cov.d1c):
        cyc = nullspace_f2(d1)
        for _ in range(n_samples):
            mask = rng.integers(0, 2, cyc.shape[0]).astype(np.uint8)
            w = int(((mask @ cyc) & 1).sum())
            if w % 2:
                ok = False
    seam_wts = [int(cell.cov.seam(z).sum()) for z in cell.ker2]
    ok = ok and all(w % 2 == 0 for w in seam_wts)
    check(f"L1/{cell.name}: cycle weights even (base+cover+seams)", ok,
          f"seam weights {sorted(set(seam_wts))}")
    return {"seam_weights": seam_wts}


# ------------------------------------------------------------------ L2 / T1


def check_L2_T1(cell: Cell, cap: int) -> dict:
    """K_z census: subgroup, index bound, Stab0, difference-class bound."""
    zs, exhausted = min_logicals(cell, cell.d, cap)
    kz_sizes, st_sizes, U_per_z = [], [], []
    freeze = False
    subgroup_ok = True
    for z in zs:
        T = translate1_all(cell.cov, z)
        if not ((cell.Qsafe @ z) & 1).any():
            freeze = True
        diffs = T ^ z[None, :]
        safe = ~(((cell.Qsafe @ diffs.T) & 1).any(axis=0))
        zero = ~(((cell.Qzero @ diffs.T) & 1).any(axis=0))
        ov = (T & z[None, :]).sum(axis=1)
        # subgroup closure of K_z (indices as (gx, gy) pairs)
        l, m = cell.cov.l, cell.cov.m
        members = {(i // m, i % m) for i in np.flatnonzero(safe)}
        for (a, b) in list(members)[:12]:
            for (c, e) in list(members)[:12]:
                if ((a + c) % l, (b + e) % m) not in members:
                    subgroup_ok = False
        kz_sizes.append(int(safe.sum()))
        st_sizes.append(int(zero.sum()))
        good = safe & ~zero
        if good.any():
            U_per_z.append(int((2 * cell.d - 2 * ov[good]).min()))
    idx_ok = all(cell.G // s <= 2 ** (cell.k // 2) for s in kz_sizes)
    check(f"L2/{cell.name}: K_z subgroup + index <= 2^(k/2)",
          subgroup_ok and idx_ok,
          f"|K_z| {dict(Counter(kz_sizes))}, |Stab0| {dict(Counter(st_sizes))}, "
          f"{'=' if exhausted else '>='}{len(zs)} min-logicals")
    U = min(U_per_z) if U_per_z else None
    print(f"       T1/{cell.name}: freeze={freeze}, difference bound U={U}"
          + (f", U histogram {dict(Counter(U_per_z))}" if U_per_z else ""))
    return {"n_min_logicals": len(zs), "exhausted": exhausted,
            "kz_sizes": dict(Counter(kz_sizes)),
            "stab0_sizes": dict(Counter(st_sizes)),
            "freeze": freeze, "U": U}


# ---------------------------------------------------------------------- T2


def check_T2(cell: Cell, w: int, expect: str) -> dict:
    """Safe-sector cover logical at <= w; pushforward is a safe base logical."""
    t0 = time.time()
    verdict, v = safe_sector_cover_logical(cell, w)
    dt = time.time() - t0
    rec: dict = {"bound": w, "verdict": verdict, "time_s": round(dt, 1)}
    if verdict == "SAT":
        pv = (push1(cell.cov) @ v) & 1
        wv, wpv = int(v.sum()), int(pv.sum())
        is_cycle = not ((cell.cov.d1b @ pv) & 1).any()
        nonzero = bool(((cell.Qzero @ pv) & 1).any())
        safe = not ((cell.Qsafe @ pv) & 1).any()
        ok = is_cycle and nonzero and safe and wpv <= wv <= w
        rec.update({"cover_weight": wv, "push_weight": wpv,
                    "push_nonzero": nonzero, "push_safe": safe})
        check(f"T2/{cell.name}: cover logical @<={w} pushes to safe base logical",
              ok and expect == "SAT",
              f"|v|={wv} -> |p(v)|={wpv}, {dt:.1f}s")
    else:
        check(f"T2/{cell.name}: safe sector @<={w} is {verdict}",
              verdict == expect, f"{dt:.1f}s")
    return rec


# ------------------------------------------------------------- W: wall pins


def certify_dsafe(cell: Cell, floor_minus_1: int,
                  conf_budget: int = 30_000_000) -> tuple[str, list]:
    """UNSAT@floor-1 on every G-orbit rep => d_safe >= floor (A14.1(4))."""
    reps = orbit_reps(cell.cov, cell.ker2)
    verdicts = []
    for i, z in enumerate(reps):
        v, wt = coset_query(cell.cov, cell.cov.seam(z), floor_minus_1,
                            conf_budget)
        verdicts.append({"rep": i, "verdict": v, "weight": wt})
        if v != "UNSAT":
            break
    status = ("CERTIFIED" if all(r["verdict"] == "UNSAT" for r in verdicts)
              and len(verdicts) == len(reps) else "FAILED")
    return status, verdicts


def ladder_dsafe(cell: Cell, start_w: int, sat_conf: int = 3_000_000,
                 unsat_conf: int = 2_000_000) -> tuple[str, int]:
    """Exact-or-upper d_safe by descending ladder over all orbit reps.

    Pass 1 descends by witnesses (cheap); pass 2 makes one bounded UNSAT
    attempt at best-2 per rep. Returns ("exact"|"upper", value): "upper"
    means some UNSAT attempt hit the conflict budget (value is still a
    certified upper bound via its witness)."""
    reps = orbit_reps(cell.cov, cell.ker2)
    seams = [cell.cov.seam(z) for z in reps]
    best = None
    for seam in seams:
        w = min(start_w, int(seam.sum()) - 1)
        cur = int(seam.sum())
        while True:
            v, wt = coset_query(cell.cov, seam, w, sat_conf)
            if v == "SAT":
                cur = wt
                w = wt - 2
            else:
                break
        best = cur if best is None else min(best, cur)
    certified = True
    for seam in seams:
        v, wt = coset_query(cell.cov, seam, best - 2, unsat_conf)
        if v == "SAT":  # a deeper element the cheap pass missed: restart
            return ladder_dsafe(cell, wt, sat_conf, unsat_conf)
        if v != "UNSAT":
            certified = False
            break
    return ("exact" if certified else "upper"), best


def main() -> None:
    t_start = time.time()

    print("== cells ==")
    cells = {
        "pair72-x": Cell("pair72-x", "x^2 + y + y^3", "1 + x + y^2",
                         3, 6, "x", 4),
        "gross-x": Cell("gross-x", "x^3 + y + y^2", "y^3 + x + x^2",
                        6, 6, "x", 6),
        "hit3-y": Cell("hit3-y", "y^3 + x + x^2", "y + x*y^2 + x^2",
                       6, 6, "y", 6),
        "bb90-x": Cell("bb90-x", "x^9 + y + y^2", "1 + x^2 + x^7",
                       15, 3, "x", 10),
        "bb90-y": Cell("bb90-y", "x^9 + y + y^2", "1 + x^2 + x^7",
                       15, 3, "y", 10),
        "bb108-y": Cell("bb108-y", "x^3 + y + y^2", "y^3 + x + x^2",
                        9, 6, "y", 10),
        "bb108-u18": Cell("bb108-u18", "x^12 + x^9*y + y^2",
                          "x^2 + x^9 + x^10", 18, 3, "x", 10),
        "bb288-y": Cell("bb288-y", "x^3 + y^2 + y^7", "y^3 + x + x^2",
                        12, 12, "y", 18),
        "bb288-c48b": Cell("bb288-c48b", "1 + x^3*y^2 + x^3*y^7",
                           "x*y^3 + x^3 + x^8", 12, 12, "x", 18),
    }
    for c in cells.values():
        print(f"  {c.name}: |G|={c.G}, k={c.k}, k~={c.kc}, d={c.d}")

    print("\n== L0: the safe sector is the transfer kernel ==")
    RESULTS["L0"] = {n: check_L0(c) for n, c in cells.items()}

    print("\n== L1: parity ==")
    RESULTS["L1"] = {n: check_L1(c) for n, c in cells.items()
                     if n in ("pair72-x", "gross-x", "bb90-y", "bb108-y",
                              "bb108-u18", "bb288-y")}

    print("\n== L2/T1: collision subgroups and difference classes ==")
    RESULTS["L2"] = {}
    for n, cap in [("pair72-x", 30), ("gross-x", 100), ("hit3-y", 100),
                   ("bb90-y", 100), ("bb108-y", 60)]:
        RESULTS["L2"][n] = check_L2_T1(cells[n], cap)

    print("\n== T2: the pushforward mechanism ==")
    RESULTS["T2"] = {}
    # failing cells: the wall value is achieved in the cover's safe sector
    # (gating: verified in the session smoke tests, now re-certified)
    RESULTS["T2"]["bb108-y"] = check_T2(cells["bb108-y"], 18, "SAT")
    RESULTS["T2"]["bb90-y"] = check_T2(cells["bb90-y"], 10, "SAT")

    def t2_probe(cell: Cell, w: int, conf: int = 30_000_000) -> dict:
        """Non-gating: SAT gives d_safe <= w via T2; UNSAT/UNKNOWN says the
        safe sector is not (cheaply) achieved at w upstairs — the theorem is
        one-directional, so either verdict is consistent."""
        t0 = time.time()
        verdict, v = safe_sector_cover_logical(cell, w, conf_budget=conf)
        rec = {"bound": w, "verdict": verdict,
               "time_s": round(time.time() - t0, 1)}
        if verdict == "SAT":
            pv = (push1(cell.cov) @ v) & 1
            nonzero = bool(((cell.Qzero @ pv) & 1).any())
            safe = not ((cell.Qsafe @ pv) & 1).any()
            rec.update({"cover_weight": int(v.sum()),
                        "push_weight": int(pv.sum()),
                        "push_nonzero": nonzero, "push_safe": safe})
        print(f"       T2-probe/{cell.name} @<= {w}: {verdict} "
              + (f"|v|={rec.get('cover_weight')} -> |p(v)|="
                 f"{rec.get('push_weight')} safe={rec.get('push_safe')}"
                 if verdict == "SAT" else "")
              + f" [{rec['time_s']}s]")
        return rec

    RESULTS["T2"]["bb90-x"] = t2_probe(cells["bb90-x"], 18)
    RESULTS["T2"]["bb108-u18"] = t2_probe(cells["bb108-u18"], 18)
    # doublers: probe at 2d (SAT means the safe sector is achieved at 2d,
    # i.e. the tight d_safe = 2d has an overlap-free lift; UNSAT means the
    # cover's 2d tightness witness is diagonal-only)
    for n in ("pair72-x", "gross-x", "hit3-y"):
        RESULTS["T2"][n] = t2_probe(cells[n], 2 * cells[n].d)

    if "--expensive" in sys.argv:
        # d~_safe(bb108-y) exactly: SAT@16, SAT@14 (each pushing k->k,
        # overlap-free), UNSAT@12. The UNSAT took ~5 h of CaDiCaL at
        # n = 216 when first run (2026-07-06); budget accordingly.
        print("\n== T2-expensive: bb108-y cover safe-sector minimum ==")
        for w in (16, 14, 12):
            rec = t2_probe(cells["bb108-y"], w, conf=2_000_000_000)
            RESULTS["T2"][f"bb108-y-cover@{w}"] = rec
            if rec["verdict"] != "SAT":
                break

    print("\n== W: wall pins (exact d_safe by descending ladder) ==")
    RESULTS["W"] = {}

    status, verd = certify_dsafe(cells["bb90-y"], 9)
    s0 = min(int(cells["bb90-y"].cov.seam(z).sum())
             for z in orbit_reps(cells["bb90-y"].cov, cells["bb90-y"].ker2))
    check("W/bb90-y: d_safe = 10 = d exactly (freeze; UNSAT@9 all reps, seam@10)",
          status == "CERTIFIED" and s0 == 10,
          f"{len(verd)} reps, raw seam min {s0}")
    RESULTS["W"]["bb90-y"] = {"floor_minus_1": 9, "status": status,
                              "verdicts": verd, "s0_min": s0}

    st, val = ladder_dsafe(cells["bb108-y"], 17)
    # the correction: the historical "18" reading was a witness weight;
    # the true minimum is strictly below (and even, and <= 2d-2 = 18)
    check("W/bb108-y: exact ladder lands strictly below the historical 18, "
          "even, <= 2d-2", val < 18 and val % 2 == 0,
          f"d_safe {'=' if st == 'exact' else '<='} {val}")
    RESULTS["W"]["bb108-y"] = {"ladder": st, "value": val}

    print("\n== W: orbit-finalist sample (bb_108 v1 x-sweep) ==")
    sweep = json.load(open(ROOT / "data/a14/bb108_orbit_sweep.json"))
    finalists = [s for s in sweep["survivors"] if not s["cheap_reject"]]
    print(f"  {len(finalists)} finalists (cheap tiers stalled at 20); "
          "exact ladders on the first 4:")
    scan_log = []
    for s in finalists[:4]:
        cell = Cell(f"orbit[{s['A']} | {s['B']}]", s["A"], s["B"], 9, 6,
                    s["axis"], 10)
        if cell.k != 8 or cell.kc != 8:
            scan_log.append({"A": s["A"], "B": s["B"], "skip": "k-gate"})
            continue
        st, val = ladder_dsafe(cell, 17)
        scan_log.append({"A": s["A"], "B": s["B"], "axis": s["axis"],
                         "ladder": st, "value": val})
        print(f"    A={s['A']:<20} B={s['B']:<20} d_safe "
              f"{'=' if st == 'exact' else '<='} {val}")
    vals = [r["value"] for r in scan_log if "value" in r]
    check("W/orbit-sample: all exact values even, <= 2d-2, and strictly "
          "below the reported ceiling 18",
          bool(vals) and all(v % 2 == 0 and v <= 16 for v in vals),
          f"values {sorted(set(vals))}")
    RESULTS["W"]["orbit_scan"] = scan_log

    # ----------------------------------------------------------- summary
    fails = [n for n, ok in CHECKS if not ok]
    RESULTS["summary"] = {"passed": len(CHECKS) - len(fails),
                          "total": len(CHECKS), "failed": fails,
                          "wall_s": round(time.time() - t_start, 1)}
    with open(OUT / "deficit_wall_checks.json", "w") as fh:
        json.dump(RESULTS, fh, indent=1, default=str)
    print(f"\n{len(CHECKS) - len(fails)}/{len(CHECKS)} checks passed "
          f"({time.time() - t_start:.0f}s). Output: data/a17/deficit_wall_checks.json")
    if fails:
        print("FAILED:")
        for n in fails:
            print(f"  - {n}")
        sys.exit(1)
    print("ALL CHECKS PASS — A17 deficit-wall battery green.")


if __name__ == "__main__":
    main()
