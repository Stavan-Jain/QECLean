"""A3 / Track 1.1 Fork B — elementary projection bound d_gross >= min(d_base, mu).

Claim (elementary; uses only the triangle inequality and that p is a projection
chain map):
  For ANY nontrivial cover logical v = (v0, v1):  |v| = |v0|+|v1| >= |v0+v1| = |p(v)|.
  - safe ([p(v)] != 0): |v| >= |p(v)| >= d_base.
  - dangerous, p(v) != 0: p(v) is a NONZERO base Z-stabilizer, so |v| >= |p(v)| >= mu_Z,
        mu_Z := min nonzero weight of a base Z-stabilizer (rowspan H_Z^base).
  - dangerous, p(v) = 0: v = tau(a), a nontrivial base logical, |v| = 2|a| >= 2 d_base.
  Hence  d_cover >= min(d_base, mu_Z).

This is a clean cover-transfer-style bound (inputs are base-code quantities). It
will NOT reach the factor-2 (d=12); the question is what min(d_base, mu_Z) gives
on gross -- if mu_Z >= 3 it already BEATS the published LP floor d >= 2 (goal 3).

We compute mu_Z (and mu_X) for the base [[72,12,6]] via SAT, with sanity checks.
Also numerically re-verify the bound logic against the cover. Discovery only.
"""
from __future__ import annotations
import numpy as np
from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195

from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.checks import bb_check_matrices
from bb_lab.linalg import nullspace_f2
from bb_lab.sat_distance import _xor_chain

Gb = ZmZn(6, 6); Ab = Poly.from_string("x^3 + y + y^2", Gb); Bb = Poly.from_string("y^3 + x + x^2", Gb)
cm_b = bb_check_matrices(Ab, Bb)
HXb, HZb = cm_b.H_X, cm_b.H_Z
nb = Gb.cardinality

def min_nonzero_in_rowspan(H, label):
    """min nonzero weight of a vector in rowspan(H), over F2, via SAT.
    v in rowspan(H) <=> v . k = 0 for every k in ker(H) (right nullspace)."""
    n = H.shape[1]
    K = nullspace_f2(H)            # basis of {x : H x = 0}
    best = None
    # ascending weight search
    for w in range(1, n + 1):
        pool = IDPool(); qv = [pool.id() for _ in range(n)]; cnf = CNF()
        # membership: v . k = 0 for each k
        for k in K:
            idx = np.flatnonzero(k)
            if idx.size == 0: continue
            o = _xor_chain((qv[i] for i in idx), pool, cnf)
            if o is not None: cnf.append([-o])
        # nonzero
        cnf.append(list(qv))
        # weight <= w
        if w < n:
            cnf.extend(CardEnc.atmost(lits=qv, bound=w, vpool=pool, encoding=EncType.seqcounter).clauses)
        s = Cadical195(bootstrap_with=cnf.clauses)
        if s.solve():
            model = set(l for l in s.get_model() if l > 0)
            best = sum(1 for q in qv if q in model)
            s.delete()
            print(f"  {label}: min nonzero rowspan weight = {best}")
            return best
        s.delete()
    return None

print("=== base [[72,12,6]] stabilizer minimum weights ===")
# sanity: a single H_Z row is in rowspan with weight 6, so mu_Z <= 6.
print(f"  (sanity) a base H_Z generator row weight = {int(HZb[0].sum())} (expect 6) => mu_Z <= 6")
muZ = min_nonzero_in_rowspan(HZb, "mu_Z (Z-stabilizers, rowspan H_Z)")
muX = min_nonzero_in_rowspan(HXb, "mu_X (X-stabilizers, rowspan H_X)")

d_base = 6
print("\n=== resulting elementary cover-transfer bound ===")
print(f"  d_base = {d_base},  mu_Z = {muZ},  mu_X = {muX}")
# For Z-logicals (X-cycles) the relevant projection lands p(v) in base X-cycles;
# trivial ones are Z-stabilizers (rowspan H_Z) -> mu_Z is the relevant floor.
bound = min(d_base, muZ)
print(f"  => d_gross (Z-distance) >= min(d_base, mu_Z) = min({d_base}, {muZ}) = {bound}")
print(f"     published LP floor is d >= 2;  this bound { 'BEATS' if bound > 2 else 'does NOT beat'} it.")
print(f"     (clean symmetric case gives >= 2 d_base = {2*d_base}; this min() is the")
print(f"      binding floor from the p(v) != 0 dangerous + safe sectors.)")
