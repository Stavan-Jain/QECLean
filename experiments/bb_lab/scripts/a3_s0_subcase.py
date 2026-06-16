"""A3 / Track 1.1 §2 — the s=0 case sub-split: does [v0]=0 bind the minimum?

In the easy case s=0, both sheets v0, v1 are base CYCLES with [v0]=[v1]=:[c].
  - [c] != 0: |v0|,|v1| >= d_base => |v| >= 2 d_base = 12 (clean analytic argument).
  - [c]  = 0: both sheets are base STABILIZERS. The cover logical v need NOT be a
    cover stabilizer (the cut-coupling can obstruct solving v = d2_cover w), so this
    subcase is not automatically trivial. Does it produce a weight-<=12 nontrivial
    dangerous logical? If UNSAT at w<=12, the [c]=0 subcase is OFF-minimum and the
    easy [c]!=0 argument carries the entire minimum.

Encoding adds to a3_s_nonzero_sat: [v0]=0 <=> (Pi0^T g_i).v = 0 for all base logX g_i,
where Pi0 picks sheet 0 (cover x<6). Sanity-checked against the s=0 SAT (which is
SAT at 12).
"""
from __future__ import annotations
import numpy as np
from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195

from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.checks import bb_check_matrices
from bb_lab.linalg import nullspace_f2, quotient_complement_basis
from bb_lab.sat_distance import _xor_chain

Gc = ZmZn(12, 6); Ac = Poly.from_string("x^3 + y + y^2", Gc); Bc = Poly.from_string("y^3 + x + x^2", Gc)
Gb = ZmZn(6, 6);  Ab = Poly.from_string("x^3 + y + y^2", Gb); Bb = Poly.from_string("y^3 + x + x^2", Gb)
cm_c = bb_check_matrices(Ac, Bc); cm_b = bb_check_matrices(Ab, Bb)
HXc, HZc = cm_c.H_X, cm_c.H_Z
HXb, HZb = cm_b.H_X, cm_b.H_Z
nc, nb = Gc.cardinality, Gb.cardinality
N = 2*nc

def base_of(g): return (g[0] % 6, g[1])
def sheet(g): return 1 if g[0] >= 6 else 0
P = np.zeros((2*nb, N), np.uint8)
Pi0 = np.zeros((2*nb, N), np.uint8)     # sheet-0 projection (cover x<6 -> base)
for g in Gc:
    gb = base_of(g)
    P[Gb.index(gb), Gc.index(g)] ^= 1
    P[nb+Gb.index(gb), nc+Gc.index(g)] ^= 1
    if g[0] < 6:
        Pi0[Gb.index(gb), Gc.index(g)] = 1
        Pi0[nb+Gb.index(gb), nc+Gc.index(g)] = 1
row_perm = np.empty(nc, dtype=int); col_perm = np.empty(2*nc, dtype=int)
for g in Gc:
    row_perm[Gc.index(g)] = sheet(g)*nb + Gb.index(base_of(g))
    for blk in (0, 1):
        col_perm[blk*nc + Gc.index(g)] = sheet(g)*(2*nb) + blk*nb + Gb.index(base_of(g))
HXc_p = np.zeros_like(HXc); HXc_p[row_perm[:, None], col_perm[None, :]] = HXc
d1c = HXc_p[:nb, 2*nb:] & 1

def logX(HX, HZ): return quotient_complement_basis(HX, nullspace_f2(HZ))
logX_b = logX(HXb, HZb); logX_c = logX(HXc, HZc)
D = np.array([(P.T @ (g & 1)) & 1 for g in logX_b], np.uint8)       # dangerous
S = (d1c @ P) & 1                                                   # s
V0 = np.array([(Pi0.T @ (g & 1)) & 1 for g in logX_b], np.uint8)    # [v0]=0 rows

def solve(weight, *, v0_trivial):
    pool = IDPool(); qv = [pool.id() for _ in range(N)]; cnf = CNF()
    def par(row): return _xor_chain((qv[i] for i in np.flatnonzero(row)), pool, cnf)
    for r in HXc:
        o = par(r & 1);  cnf.append([-o]) if o is not None else None
    for r in D:
        o = par(r);      cnf.append([-o]) if o is not None else None
    for r in S:                                  # s = 0
        o = par(r);      cnf.append([-o]) if o is not None else None
    outs = [par(L & 1) for L in logX_c]; cnf.append([o for o in outs if o is not None])  # nontrivial
    if v0_trivial:
        for r in V0:
            o = par(r);  cnf.append([-o]) if o is not None else None
    if weight < N:
        cnf.extend(CardEnc.atmost(lits=qv, bound=weight, vpool=pool, encoding=EncType.seqcounter).clauses)
    s = Cadical195(bootstrap_with=cnf.clauses); sat = s.solve(); s.delete()
    return sat

print("sanity: dangerous & nontrivial & s=0 (no [v0]=0), w<=12 :", solve(12, v0_trivial=False), "(expect True)")
print("sanity: same, w<=11                                     :", solve(11, v0_trivial=False), "(expect False)")
print()
for w in (11, 12, 13, 14):
    print(f"[c]=0 subcase: dangerous & nontrivial & s=0 & [v0]=0, w<={w:2d} : {solve(w, v0_trivial=True)}")
print("\nUNSAT at w<=12 => [c]=0 subcase is off-minimum; the [c]!=0 argument")
print("carries the whole s=0 minimum. SAT at 12 => [c]=0 must be handled at min.")
