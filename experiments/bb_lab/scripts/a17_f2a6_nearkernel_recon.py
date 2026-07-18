"""A17 dangerous discharge, step 5: recon of the near-kernel light-boundary
family that the cutoff query exposed (min-rep weight 33, |b| = 10).

Questions:
  1. structure of the found model: |A*f| vs |B*f|, distance of f to
     ker MA / ker MB, component (idempotent) profile;
  2. mu_Z sharpening: is there ANY nonzero boundary with |b| <= 4?
     (would undercut the weight-6 stabilizer floor / small-cycle picture)
  3. how far down does the no-small-preimage family go: minimize |b| over
     f with all coset reps >= 5;
  4. count blocking-clause samples of the family at |b| = 10 to see orbit
     structure (translates? A-line unions?).

Usage: uv run python scripts/a17_f2a6_nearkernel_recon.py
"""

from __future__ import annotations

import sys
import time
from pathlib import Path

import numpy as np

LAB_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LAB_ROOT / "src"))

from bb_lab.group import AbelianGroup
from bb_lab.poly import Poly
from bb_lab.checks import circulant
from bb_lab.linalg import nullspace_f2, rank_f2

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195

A_STR, B_STR = "1 + y + x", "x*y^6 + x*y^10 + x^2*y^12"
ELL, M = 5, 15

Gb = AbelianGroup((ELL, M))
nb = Gb.cardinality
Ab, Bb = Poly.from_string(A_STR, Gb), Poly.from_string(B_STR, Gb)
MAb, MBb = circulant(Ab).astype(np.uint8), circulant(Bb).astype(np.uint8)
D2b = np.vstack([MAb, MBb]) % 2
kerb = nullspace_f2(D2b).astype(np.uint8)
kerA = nullspace_f2(MAb).astype(np.uint8)
kerB = nullspace_f2(MBb).astype(np.uint8)
print(f"dim ker MA = {kerA.shape[0]}, dim ker MB = {kerB.shape[0]}, "
      f"dim ker d2 = {kerb.shape[0]}")

ker_elems = []
for mask in range(16):
    z = np.zeros(nb, dtype=np.uint8)
    for i in range(4):
        if (mask >> i) & 1:
            z ^= kerb[i]
    ker_elems.append(z)


def dist_to_span(rows: np.ndarray, v: np.ndarray) -> int:
    """Min weight of v + span(rows), exhaustive over 2^dim (dim <= 8)."""
    d = rows.shape[0]
    best = None
    for mask in range(1 << d):
        w = v.copy()
        for i in range(d):
            if (mask >> i) & 1:
                w = w ^ rows[i]
        wt = int(w.sum())
        best = wt if best is None or wt < best else best
    return best


def build_query(light_cap: int, min_rep: int | None):
    pool = IDPool()
    fvar = [pool.id(f"f{i}") for i in range(nb)]
    bvar = [pool.id(f"b{j}") for j in range(2 * nb)]
    cnf = CNF()
    for j in range(2 * nb):
        ins = [fvar[i] for i in np.nonzero(D2b[j])[0]]
        lits = [bvar[j], *ins]
        for m in range(16):
            neg = [(-1) ** ((m >> k) & 1) for k in range(4)]
            if sum(1 for x in neg if x < 0) % 2 == 1:
                cnf.append([neg[k] * lits[k] for k in range(4)])
    cnf.extend(CardEnc.atmost(lits=bvar, bound=light_cap, vpool=pool,
                              encoding=EncType.seqcounter))
    cnf.append(bvar)
    if min_rep is not None:
        for z in ker_elems:
            lits = [(-fvar[i] if z[i] else fvar[i]) for i in range(nb)]
            cnf.extend(CardEnc.atleast(lits=lits, bound=min_rep, vpool=pool,
                                       encoding=EncType.seqcounter))
    return cnf, fvar, bvar


def solve(cnf, fvar, name, blocking_rounds: int = 0):
    sols = []
    t0 = time.time()
    with Cadical195(bootstrap_with=cnf.clauses) as s:
        for _ in range(blocking_rounds + 1):
            if not s.solve():
                print(f"  {name}: UNSAT ({time.time() - t0:.1f} s)")
                return sols
            model = s.get_model()
            f = np.zeros(nb, dtype=np.uint8)
            for i in range(nb):
                if model[fvar[i] - 1] > 0:
                    f[i] = 1
            sols.append(f)
            # block this exact f
            s.add_clause([(-fvar[i] if f[i] else fvar[i]) for i in range(nb)])
    print(f"  {name}: {len(sols)} model(s) ({time.time() - t0:.1f} s)")
    return sols


print("== 1. structure of the min-rep>=4 |b|<=14 family ==")
cnf, fvar, bvar = build_query(14, 4)
sols = solve(cnf, fvar, "minrep4_cap14", blocking_rounds=4)
elems_b = list(Gb)
for f in sols:
    bA = (MAb @ f) % 2
    bB = (MBb @ f) % 2
    dA = dist_to_span(kerA, f)
    dB = dist_to_span(kerB, f)
    coset_min = min(int((f ^ z).sum()) for z in ker_elems)
    print(f"  |f|={int(f.sum())} coset_min={coset_min} |A*f|={int(bA.sum())} "
          f"|B*f|={int(bB.sum())}  dist(f,kerA)={dA} dist(f,kerB)={dB}")

print("== 2. mu_Z probe: any nonzero boundary with |b| <= 4? ==")
cnf2, fvar2, _ = build_query(4, None)
sols2 = solve(cnf2, fvar2, "mu_cap4")
for f in sols2:
    print(f"  FOUND |b|={int(((D2b @ f) % 2).sum())} |f|={int(f.sum())}")

print("== 3. minimum |b| over the no-small-preimage family (min_rep 5) ==")
for cap in (4, 6, 8):
    cnfc, fvarc, _ = build_query(cap, 5)
    solsc = solve(cnfc, fvarc, f"minrep5_cap{cap}")
    if solsc:
        f = solsc[0]
        print(f"    model: |b|={int(((D2b @ f) % 2).sum())}, |f|={int(f.sum())}")
        break
