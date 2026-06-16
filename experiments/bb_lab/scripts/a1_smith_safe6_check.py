"""Adversarial verification of the weight-6 safe-sector logical and its projection.

If a weight-6 cover X-logical exists with pr_*!=0, then:
  - p(L~) is a nontrivial base class with |p(L~)| <= 6.
  - d_base = 6 forces |p(L~)| = 6, and |L~| >= |p(L~)| only via p weight-nonincreasing.
This would mean the SAFE branch is TIGHT at 6: it proves d_cover >= 6 and that's all.
We extract the actual witness and check every claim, plus the d_base=6 fact independently.
"""
from __future__ import annotations
import numpy as np
from pysat.card import CardEnc
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195

from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.checks import bb_check_matrices
from bb_lab.linalg import nullspace_f2, quotient_complement_basis, rank_f2

Gc = ZmZn(12, 6); Ac = Poly.from_string("x^3 + y + y^2", Gc); Bc = Poly.from_string("y^3 + x + x^2", Gc)
Gb = ZmZn(6, 6);  Ab = Poly.from_string("x^3 + y + y^2", Gb); Bb = Poly.from_string("y^3 + x + x^2", Gb)
cm_c = bb_check_matrices(Ac, Bc); cm_b = bb_check_matrices(Ab, Bb)
nc, nb = Gc.cardinality, Gb.cardinality
HXc, HZc = cm_c.H_X, cm_c.H_Z
HXb, HZb = cm_b.H_X, cm_b.H_Z

P = np.zeros((2*nb, 2*nc), dtype=np.uint8)
for gt in Gc:
    gb = tuple(gi % o for gi, o in zip(gt, Gb.orders))
    P[Gb.index(gb), Gc.index(gt)] ^= 1
    P[nb+Gb.index(gb), nc+Gc.index(gt)] ^= 1

ker_HZc = nullspace_f2(HZc); logX_c = quotient_complement_basis(HXc, ker_HZc)
ker_HZb = nullspace_f2(HZb); logX_b = quotient_complement_basis(HXb, ker_HZb)
pull = (logX_b @ P) & 1

def xor_chain(lits, pool, cnf):
    seq = list(lits)
    if not seq: return None
    acc = seq[0]
    for x in seq[1:]:
        new = pool.id()
        cnf.append([-new,-acc,-x]); cnf.append([-new,acc,x]); cnf.append([new,-acc,x]); cnf.append([new,acc,-x])
        acc = new
    return acc
def parity(row, vvars, pool, cnf):
    return xor_chain([vvars[i] for i in np.flatnonzero(row & 1)], pool, cnf)

# find a weight-6 safe witness
pool = IDPool(); vvars = [pool.id() for _ in range(2*nc)]; cnf = CNF()
for r in range(HZc.shape[0]):
    out = parity(HZc[r], vvars, pool, cnf)
    if out is not None: cnf.append([-out])
nt = [o for j in range(logX_c.shape[0]) if (o:=parity(logX_c[j], vvars, pool, cnf)) is not None]
cnf.append(nt)
djs = [parity(pull[j], vvars, pool, cnf) for j in range(pull.shape[0])]
cnf.append([o for o in djs if o is not None])  # safe: pr_*!=0
cnf.extend(CardEnc.atmost(lits=list(vvars), bound=6, vpool=pool).clauses)
s = Cadical195(bootstrap_with=cnf.clauses)
assert s.solve(), "no weight-6 safe logical?!"
model = s.get_model(); s.delete()
v = np.zeros(2*nc, dtype=np.uint8)
for i in range(2*nc):
    if model[vvars[i]-1] > 0: v[i] = 1
print(f"weight-6 safe witness: |L~| = {int(v.sum())}")
print(f"  is X-cycle (H_Z^c v=0): {not np.any((HZc@v)&1)}")
print(f"  nontrivial cover logical (anticommutes some logX_c): {np.any((logX_c@v)&1)}")
pv = (P@v)&1
print(f"  |p(L~)| = {int(pv.sum())}")
print(f"  p(L~) is base X-cycle (H_Z^b p(v)=0): {not np.any((HZb@pv)&1)}")
print(f"  p(L~) nontrivial base class (anticommutes some logX_b): {np.any((logX_b@pv)&1)}")

# independent d_base check: min weight nontrivial base logical
def min_base():
    for w in range(1, 9):
        p2 = IDPool(); vv = [p2.id() for _ in range(2*nb)]; c2 = CNF()
        for r in range(HZb.shape[0]):
            o = parity(HZb[r], vv, p2, c2)
            if o is not None: c2.append([-o])
        ntb = [o for j in range(logX_b.shape[0]) if (o:=parity(logX_b[j], vv, p2, c2)) is not None]
        c2.append(ntb)
        c2.extend(CardEnc.atmost(lits=list(vv), bound=w, vpool=p2).clauses)
        ss = Cadical195(bootstrap_with=c2.clauses); r2 = ss.solve(); ss.delete()
        if r2: return w
    return ">8"
print(f"\nindependent d_base ([[72,12,6]]) = {min_base()}")
print("\nINTERPRETATION:")
print("  Safe branch bound: |L~| >= |p(L~)| >= d_base. Here |p(L~)|=6=d_base and |L~|=6.")
print("  => the safe branch is TIGHT at 6; it CANNOT exceed d_base on its own sector.")
print("  => reaching d_cover=12 requires the DANGEROUS (pr=0) sector min=12, i.e. the")
print("     Smith connecting-map weight control through Delta=cap-omega is the ONLY route")
print("     to anything above 6. The safe branch alone gives exactly d_base.")
