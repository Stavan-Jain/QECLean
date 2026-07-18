"""A17 near-kernel classification, step 2: EXHAUSTIVE enumeration of the
light boundaries of the f2a6f17e base — all weight-<=14 codewords of the
[150, 71, 6] code im d2, up to translation.

Method: SAT with translation-orbit blocking.  Loop:
  solve (|b| <= 14, b != 0, no blocked class);
  numpy-verify the model; canonicalize its translation class;
  append the class record to the checkpoint jsonl;
  add 75 blocking clauses (one per translate, each the 150-literal
  "not this b" clause);
until UNSAT — at which point the class list is COMPLETE (solver-grade;
the final UNSAT run with all blockings is DRAT-able for the proof-grade
upgrade).

The 94 small-preimage classes from the census must all reappear (smoke
cross-check); everything else is the near-kernel stratum.  Per class we
record |b|, the (|u|, |v|) block split, the preimage-coset minimum
weight, and the support (canonical translate).

Resumable: reloads the checkpoint and re-adds blockings on restart.
Cap: --max-rounds (default 3000) as a runaway stop; hitting it is itself
a finding (the stratum is large), recorded in the tail record.

Usage: uv run python scripts/a17_f2a6_light_enum.py [--max-rounds N]
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

from bb_lab.group import AbelianGroup
from bb_lab.poly import Poly
from bb_lab.checks import circulant
from bb_lab.linalg import nullspace_f2, rref_f2

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195

A_STR, B_STR = "1 + y + x", "x*y^6 + x*y^10 + x^2*y^12"
ELL, M = 5, 15
CAP = 14

Gb = AbelianGroup((ELL, M))
nb = Gb.cardinality
Ab, Bb = Poly.from_string(A_STR, Gb), Poly.from_string(B_STR, Gb)
MAb, MBb = circulant(Ab).astype(np.uint8), circulant(Bb).astype(np.uint8)
D2b = np.vstack([MAb, MBb]) % 2
elems_b = list(Gb)
base_idx = {g: i for i, g in enumerate(Gb)}
kerb = nullspace_f2(D2b).astype(np.uint8)
ker_elems = []
for mask in range(16):
    z = np.zeros(nb, dtype=np.uint8)
    for i in range(4):
        if (mask >> i) & 1:
            z ^= kerb[i]
    ker_elems.append(z)


def solve_f2(Amat: np.ndarray, b: np.ndarray) -> np.ndarray | None:
    Amat = Amat.astype(np.uint8) % 2
    aug = np.hstack([Amat, (b.astype(np.uint8) % 2)[:, None]])
    R, piv = rref_f2(aug)
    ncols = Amat.shape[1]
    if ncols in piv:
        return None
    x = np.zeros(ncols, dtype=np.uint8)
    for r, c in enumerate(piv):
        x[c] = R[r, ncols]
    return x


# translation action on 1-chains (blocks translate together)
TRANS = []
for tx in range(ELL):
    for ty in range(M):
        perm = np.zeros(2 * nb, dtype=np.int64)
        for i, (gx, gy) in enumerate(elems_b):
            j = base_idx[((gx + tx) % ELL, (gy + ty) % M)]
            perm[i] = j
            perm[nb + i] = nb + j
        TRANS.append(perm)


def translates(b: np.ndarray):
    for perm in TRANS:
        out = np.zeros_like(b)
        out[perm] = b
        yield out


def canonical(b: np.ndarray) -> tuple[bytes, np.ndarray]:
    best = None
    for tb in translates(b):
        key = tb.tobytes()
        if best is None or key < best[0]:
            best = (key, tb)
    return best


# ------------------------------------------------------------- CNF
pool = IDPool()
fvar = [pool.id(f"f{i}") for i in range(nb)]
bvar = [pool.id(f"b{j}") for j in range(2 * nb)]
cnf = CNF()
for j in range(2 * nb):
    ins = [fvar[i] for i in np.nonzero(D2b[j])[0]]
    lits = [bvar[j], *ins]
    for m in range(16):
        neg = [(-1) ** ((m >> k) & 1) for k in range(4)]
        if sum(1 for x_ in neg if x_ < 0) % 2 == 1:
            cnf.append([neg[k] * lits[k] for k in range(4)])
cnf.extend(CardEnc.atmost(lits=bvar, bound=CAP, vpool=pool,
                          encoding=EncType.seqcounter))
cnf.append(bvar)


def block_clause(tb: np.ndarray) -> list[int]:
    return [(-bvar[j] if tb[j] else bvar[j]) for j in range(2 * nb)]


OUT = LAB_ROOT / "data" / "a15" / "f2a6_light_classes.jsonl"


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-rounds", type=int, default=3000)
    args = ap.parse_args()

    known: list[dict] = []
    if OUT.exists():
        with open(OUT) as fh:
            known = [json.loads(l) for l in fh if l.strip()]
        known = [r for r in known if "b_support" in r]
        print(f"resuming with {len(known)} known classes", flush=True)

    solver = Cadical195(bootstrap_with=cnf.clauses)
    for rec in known:
        b = np.zeros(2 * nb, dtype=np.uint8)
        for blk, gx, gy in rec["b_support"]:
            b[blk * nb + base_idx[(gx, gy)]] = 1
        for tb in translates(b):
            solver.add_clause(block_clause(tb))

    n = len(known)
    t_start = time.time()
    while n < args.max_rounds:
        t0 = time.time()
        if not solver.solve():
            dt = time.time() - t0
            print(f"UNSAT after {n} classes ({dt:.1f} s final call; "
                  f"{time.time() - t_start:.0f} s total) — COMPLETE",
                  flush=True)
            with open(OUT, "a") as fh:
                fh.write(json.dumps({"complete": True, "n_classes": n,
                                     "final_unsat_secs": round(dt, 1)}) + "\n")
            return
        model = solver.get_model()
        f = np.zeros(nb, dtype=np.uint8)
        for i in range(nb):
            if model[fvar[i] - 1] > 0:
                f[i] = 1
        u = (MAb @ f) % 2
        v = (MBb @ f) % 2
        b = np.concatenate([u, v])
        w = int(b.sum())
        assert 0 < w <= CAP, w
        _, cb = canonical(b)
        # preimage coset minimum (solve d2 f = cb for the canonical rep)
        fc = solve_f2(D2b, cb)
        assert fc is not None
        coset_min = min(int((fc ^ z).sum()) for z in ker_elems)
        rec = {
            "b_weight": w,
            "u_weight": int(cb[:nb].sum()),
            "v_weight": int(cb[nb:].sum()),
            "coset_min": coset_min,
            "b_support": [[int(j // nb), *elems_b[j % nb]]
                          for j in np.nonzero(cb)[0]],
        }
        with open(OUT, "a") as fh:
            fh.write(json.dumps(rec) + "\n")
        n += 1
        if n % 25 == 0 or coset_min >= 5:
            print(f"  class {n}: |b|={w} ({rec['u_weight']}|{rec['v_weight']})"
                  f" coset_min={coset_min} [{time.time() - t0:.1f} s]",
                  flush=True)
        for tb in translates(cb):
            solver.add_clause(block_clause(tb))
    print(f"MAX ROUNDS {args.max_rounds} hit — stratum larger than cap; "
          f"{n} classes so far", flush=True)
    with open(OUT, "a") as fh:
        fh.write(json.dumps({"complete": False, "n_classes": n}) + "\n")


if __name__ == "__main__":
    main()
