"""A15 dangerous-sector discharge, step 4: the rep-weight cutoff certificate.

Claim to certify: every nonzero light boundary (|d2 f| <= 14) of the
f2a6f17e base has a preimage of support <= 3 (the census found light
classes only at |f| in {1,2,3}; |f| = 4 contributed none).

SAT query (expect UNSAT): exists f in F2^75 with
    (a) 0 < |d2 f| <= 14,
    (b) |f + zeta| >= 4 for ALL 16 zeta in ker d2
        (i.e. b has NO preimage of support <= 3).

UNSAT => cutoff m* = 3 => the census + rung table is a COMPLETE
classification of the light-boundary dispatch.  Backends: pysat-CaDiCaL
(fast), kissat binary on the exported CNF (DRAT-able, proof-grade leg).
Any SAT model is re-verified in numpy and dumped (it would mean a census
bug — the census enumerated all |f| <= 4 supports exhaustively).

Usage: uv run python scripts/a15_f2a6_dangerous_cutoff.py [--kissat]
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
from bb_lab.linalg import nullspace_f2

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195

A_STR, B_STR = "1 + y + x", "x*y^6 + x*y^10 + x^2*y^12"
ELL, M = 5, 15
LIGHT_CAP = 14
MIN_REP = 4          # forbid any rep of weight <= MIN_REP - 1

Gb = AbelianGroup((ELL, M))
nb = Gb.cardinality
Ab, Bb = Poly.from_string(A_STR, Gb), Poly.from_string(B_STR, Gb)
MAb, MBb = circulant(Ab).astype(np.uint8), circulant(Bb).astype(np.uint8)
D2b = np.vstack([MAb, MBb]) % 2
kerb = nullspace_f2(D2b).astype(np.uint8)
assert kerb.shape[0] == 4
ker_elems = []
for mask in range(16):
    z = np.zeros(nb, dtype=np.uint8)
    for i in range(4):
        if (mask >> i) & 1:
            z ^= kerb[i]
    ker_elems.append(z)

pool = IDPool()
fvar = [pool.id(f"f{i}") for i in range(nb)]
bvar = [pool.id(f"b{j}") for j in range(2 * nb)]
cnf = CNF()

def xor_clauses(out, ins):
    """`out <-> XOR(ins)` for |ins| = 3: the 4-var parity constraint
    `out + a + b + c = 0`, as its 8 odd-negation clauses."""
    lits = [out, *ins]
    for m in range(16):
        neg = [(-1) ** ((m >> k) & 1) for k in range(4)]
        if sum(1 for x in neg if x < 0) % 2 == 0:
            continue  # keep only odd-negation clauses: forbids XOR != 0
        cnf.append([neg[k] * lits[k] for k in range(4)])

# b_j definitions: each row of D2b has weight exactly 3
for j in range(2 * nb):
    ins = [fvar[i] for i in np.nonzero(D2b[j])[0]]
    assert len(ins) == 3
    xor_clauses(bvar[j], ins)

# (a) |b| <= 14 and b != 0
cnf.extend(CardEnc.atmost(lits=bvar, bound=LIGHT_CAP, vpool=pool,
                          encoding=EncType.seqcounter))
cnf.append(bvar)  # at least one image bit

# (b) every coset rep has weight >= MIN_REP:
# |f + zeta| >= MIN_REP  <=>  at most (75 - MIN_REP) of the LITERALS
# (f_i negated on supp zeta) are FALSE  <=> at least MIN_REP true
for z in ker_elems:
    lits = [(-fvar[i] if z[i] else fvar[i]) for i in range(nb)]
    cnf.extend(CardEnc.atleast(lits=lits, bound=MIN_REP, vpool=pool,
                               encoding=EncType.seqcounter))

print(f"CNF: {cnf.nv} vars, {len(cnf.clauses)} clauses")
cnf_path = LAB_ROOT / "data" / "a15" / "f2a6_cutoff_minrep4.cnf"
cnf.to_file(str(cnf_path))
print(f"exported {cnf_path}")

t0 = time.time()
with Cadical195(bootstrap_with=cnf.clauses) as solver:
    sat = solver.solve()
    dt = time.time() - t0
    print(f"CaDiCaL: {'SAT' if sat else 'UNSAT'} in {dt:.1f} s")
    if sat:
        model = solver.get_model()
        f = np.zeros(nb, dtype=np.uint8)
        for i in range(nb):
            if model[fvar[i] - 1] > 0:
                f[i] = 1
        b = (D2b @ f) % 2
        wts = sorted(int((f ^ z).sum()) for z in ker_elems)
        print(f"  numpy re-check: |b| = {int(b.sum())} (<=14 and !=0: "
              f"{0 < int(b.sum()) <= 14}), coset weights {wts[:4]}...")
        print("  -> CENSUS GAP — investigate before trusting the dispatch!")
        sys.exit(2)

print("UNSAT => cutoff m* = 3 certified (solver-grade): every light")
print("boundary has a support-<=3 preimage; the census dispatch is complete.")
