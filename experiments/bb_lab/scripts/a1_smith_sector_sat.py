"""Rigorous min-weight on the dangerous (pr_*=0) sector vs the safe (pr_*!=0) sector.

Builds two constrained min-weight SAT problems over the 144 cover qubits:
  common: H_Z^cover . v = 0 (v is an X-cycle).
  dangerous sector: v is a NONTRIVIAL logical AND lies in ker(pr_*), i.e. its base
      class is trivial. Concretely pr_*[v]=0 means: for each of the 6 'safe' logical-Z
      base functionals f (a basis of im(pr_*)^* pulled back), <f_pulledback, v> = 0.
      Cleaner: p(v) must be a base STABILIZER (in rowspan H_Z^base) OR zero. We encode
      "the base class of p(v) is trivial" by requiring p(v) commute-test against the
      base logical-X reps gives all-zero (i.e. p(v) anticommutes with NO base logical).
  safe sector: v nontrivial AND pr_*[v] != 0 (at least one base-logical pairing is 1).

We want: min weight over (dangerous nontrivial) and min weight over (safe nontrivial).
True d_cover = 12. If dangerous-min = 12 and safe-min > 12, then the minimum-weight
logicals are ENTIRELY in the dangerous sector => Track 1.1's pr=0 branch is the
binding constraint for d=12 and weight control through Delta is unavoidable to reach 12.
If safe-min = 12 too, the safe branch (d>=6 only, since p halves) still cannot certify
12 by itself -- it only gives >= d_base.
"""
from __future__ import annotations
import numpy as np
from pysat.card import CardEnc
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195

from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.checks import bb_check_matrices
from bb_lab.linalg import nullspace_f2, quotient_complement_basis

Gc = ZmZn(12, 6); Ac = Poly.from_string("x^3 + y + y^2", Gc); Bc = Poly.from_string("y^3 + x + x^2", Gc)
Gb = ZmZn(6, 6);  Ab = Poly.from_string("x^3 + y + y^2", Gb); Bb = Poly.from_string("y^3 + x + x^2", Gb)
cm_c = bb_check_matrices(Ac, Bc); cm_b = bb_check_matrices(Ab, Bb)
nc, nb = Gc.cardinality, Gb.cardinality
HXc, HZc = cm_c.H_X, cm_c.H_Z
HXb, HZb = cm_b.H_X, cm_b.H_Z

# projection matrix on C1
P = np.zeros((2*nb, 2*nc), dtype=np.uint8)
for gt in Gc:
    gb = tuple(gi % o for gi, o in zip(gt, Gb.orders))
    P[Gb.index(gb), Gc.index(gt)] ^= 1
    P[nb+Gb.index(gb), nc+Gc.index(gt)] ^= 1

# cover logical-Z reps and base logical-X reps
ker_HXc = nullspace_f2(HXc)
logZ_c = quotient_complement_basis(HZc, ker_HXc)            # cover X-logicals (anticommute witnesses are logZ via H_X dual)
# base logical-X reps: ker(H_Z^base)/rowspan(H_X^base)
ker_HZb = nullspace_f2(HZb)
logX_b = quotient_complement_basis(HXb, ker_HZb)            # base logical-X reps; pairing <logX_b, p(v)> detects base class
print(f"#cover logZ reps = {logZ_c.shape[0]}, #base logX reps = {logX_b.shape[0]}")

# The base class of p(v) is nontrivial iff <logX_b[j], p(v)> = 1 for some j
#   = < P^T logX_b[j], v >.  Pullback functionals:
pull = (logX_b @ P) & 1     # shape (12, 2nc): pull[j] . v = <logX_b[j], p(v)>
# also need v to be nontrivial as a COVER logical: <logX_c[j], v>=1 for some j
ker_HZc = nullspace_f2(HZc)
logX_c = quotient_complement_basis(HXc, ker_HZc)
print(f"#cover logX reps = {logX_c.shape[0]}")

def xor_chain(lits, pool, cnf):
    seq = list(lits)
    if not seq: return None
    acc = seq[0]
    for x in seq[1:]:
        new = pool.id()
        cnf.append([-new,-acc,-x]); cnf.append([-new,acc,x]); cnf.append([new,-acc,x]); cnf.append([new,acc,-x])
        acc = new
    return acc

def parity_literal(row, vvars, pool, cnf):
    lits = [vvars[i] for i in np.flatnonzero(row & 1)]
    return xor_chain(lits, pool, cnf)

def build_base(sector, weight, vvars, pool, cnf):
    # H_Z^cover . v = 0 (cycle)
    for r in range(HZc.shape[0]):
        out = parity_literal(HZc[r], vvars, pool, cnf)
        if out is not None: cnf.append([-out])
    # nontrivial COVER logical: OR_j (<logX_c[j], v> = 1)
    nt = []
    for j in range(logX_c.shape[0]):
        out = parity_literal(logX_c[j], vvars, pool, cnf)
        if out is None:
            continue
        nt.append(out)
    cnf.append(nt)  # at least one anticommutation
    # sector constraint via pull functionals d_j := <pull[j], v>
    djs = []
    for j in range(pull.shape[0]):
        out = parity_literal(pull[j], vvars, pool, cnf)
        # pull[j] could be all-zero row -> out None -> functional is constant 0
        djs.append(out)
    if sector == "dangerous":
        # all base pairings 0: each d_j = 0
        for out in djs:
            if out is not None: cnf.append([-out])
    elif sector == "safe":
        # at least one base pairing = 1
        clause = [out for out in djs if out is not None]
        if not clause:
            return False  # safe sector empty (no nonconstant functional) -> infeasible
        cnf.append(clause)
    # cardinality <= weight
    card = CardEnc.atmost(lits=list(vvars), bound=weight, vpool=pool)
    cnf.extend(card.clauses)
    return True

def min_weight(sector, lo=1, hi=14):
    for w in range(lo, hi+1):
        pool = IDPool()
        vvars = [pool.id() for _ in range(2*nc)]
        cnf = CNF()
        ok = build_base(sector, w, vvars, pool, cnf)
        if not ok:
            return None
        s = Cadical195(bootstrap_with=cnf.clauses)
        sat = s.solve()
        s.delete()
        if sat:
            return w
    return f">{hi}"

print("\n=== rigorous sector minimum weights (SAT) ===")
print(f"dangerous (pr_*=0) sector  min nontrivial-logical weight = {min_weight('dangerous')}")
print(f"safe      (pr_*!=0) sector min nontrivial-logical weight = {min_weight('safe')}")
