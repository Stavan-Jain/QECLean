"""A3 / Track 1.1 §2 — RIGOROUS decision: does s != 0 bind the minimum?

Replaces the buggy scout a1_smith_sector_sat.py (whose "safe min = 6" violated
the d=12 certificate). Every encoding choice here is validated by a SANITY
LADDER first: the encoding must reproduce d_cover = 12 with the sector
constraints removed, or it is not trusted.

Decision question: is there a weight-12 dangerous NONTRIVIAL logical with
seam-syndrome s != 0?  (s = d1c . p(v), linear in v.)
  - UNSAT at weight 12  =>  every s!=0 dangerous logical has weight >= 13, i.e.
    the minimum (12) is carried entirely by the easy s=0 case. Big de-risking.
  - SAT at weight 12     =>  the hard seam-leakage case binds the minimum;
    months estimate stands.

Encoding (all parities Tseitin-encoded via sat_distance._xor_chain):
  cycle:       H_X^cover . v = 0                          (72 parities = 0)
  dangerous:   (P^T g_i) . v = 0 for each base logX g_i   (12 parities = 0)
               [ <g_i, p(v)> = 0 for all base logicals <=> [p(v)]=0 in H1(base) ]
  nontrivial:  OR_a (L_a . v = 1) over cover logX reps     (>=1 parity = 1)
  s != 0:      OR_j ((d1c P)_j . v = 1)                     (>=1 parity = 1)
  weight:      sum v <= w

Discovery/validation only; never load-bearing.
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
N = 2*nc  # 144 cover qubits

def base_of(g): return (g[0] % 6, g[1])
def sheet(g): return 1 if g[0] >= 6 else 0

# projection P: cover C1 (144) -> base C1 (72)
P = np.zeros((2*nb, N), np.uint8)
for g in Gc:
    gb = base_of(g)
    P[Gb.index(gb), Gc.index(g)] ^= 1
    P[nb+Gb.index(gb), nc+Gc.index(g)] ^= 1

# seam part d1c of base H_X (via verified permutation)
row_perm = np.empty(nc, dtype=int); col_perm = np.empty(2*nc, dtype=int)
for g in Gc:
    row_perm[Gc.index(g)] = sheet(g)*nb + Gb.index(base_of(g))
    for blk in (0, 1):
        col_perm[blk*nc + Gc.index(g)] = sheet(g)*(2*nb) + blk*nb + Gb.index(base_of(g))
HXc_p = np.zeros_like(HXc); HXc_p[row_perm[:, None], col_perm[None, :]] = HXc
d1c = HXc_p[:nb, 2*nb:] & 1            # 36 x 72

# logical reps
def logX(HX, HZ):  # X-type logicals: ker(H_Z)/rowspan(H_X)
    return quotient_complement_basis(HX, nullspace_f2(HZ))
logX_b = logX(HXb, HZb)                # 12 base X-logicals (72-vectors)
logX_c = logX(HXc, HZc)                # 12 cover X-logicals (144-vectors)

# dangerous constraint rows D = P^T g_i  (144-vectors)
D = np.array([(P.T @ (g & 1)) & 1 for g in logX_b], dtype=np.uint8)   # 12 x 144
# s!=0 constraint rows S = d1c @ P  (36 x 144)
S = (d1c @ P) & 1                                                      # 36 x 144

def solve(weight, *, dangerous, nontrivial, s_constraint):
    """s_constraint in {None, 'zero', 'nonzero'}. Returns (sat, witness_weight)."""
    pool = IDPool(); qv = [pool.id() for _ in range(N)]; cnf = CNF()
    def parity(row):
        return _xor_chain((qv[i] for i in np.flatnonzero(row)), pool, cnf)
    # cycle = 0
    for r in HXc:
        o = parity(r & 1)
        if o is not None: cnf.append([-o])
    # dangerous = 0
    if dangerous:
        for r in D:
            o = parity(r)
            if o is not None: cnf.append([-o])
    # nontrivial: OR_a (L_a . v = 1)
    if nontrivial:
        outs = [parity(L & 1) for L in logX_c]
        outs = [o for o in outs if o is not None]
        cnf.append(outs)
    # s constraint
    if s_constraint == 'zero':
        for r in S:
            o = parity(r)
            if o is not None: cnf.append([-o])
    elif s_constraint == 'nonzero':
        outs = [parity(r) for r in S]
        outs = [o for o in outs if o is not None]
        cnf.append(outs)
    # weight <= w
    if weight < N:
        card = CardEnc.atmost(lits=qv, bound=weight, vpool=pool, encoding=EncType.seqcounter)
        cnf.extend(card.clauses)
    s = Cadical195(bootstrap_with=cnf.clauses)
    sat = s.solve()
    w = None
    if sat:
        model = set(l for l in s.get_model() if l > 0)
        w = sum(1 for q in qv if q in model)
    s.delete()
    return sat, w

print("=== SANITY LADDER (encoding must reproduce d_cover = 12) ===")
sat, w = solve(11, dangerous=False, nontrivial=True, s_constraint=None)
print(f"  nontrivial, w<=11        : SAT={sat}  (expect False; d=12)")
sat, w = solve(12, dangerous=False, nontrivial=True, s_constraint=None)
print(f"  nontrivial, w<=12        : SAT={sat} (w={w})  (expect True)")
sat, w = solve(11, dangerous=True, nontrivial=True, s_constraint=None)
print(f"  dangerous, w<=11         : SAT={sat}  (expect False)")
sat, w = solve(12, dangerous=True, nontrivial=True, s_constraint=None)
print(f"  dangerous, w<=12         : SAT={sat} (w={w})  (expect True)")
sat, w = solve(12, dangerous=True, nontrivial=True, s_constraint='zero')
print(f"  dangerous & s=0, w<=12   : SAT={sat} (w={w})  (expect True; the reps)")

print("\n=== DECISION: dangerous & nontrivial & s!=0 ===")
for w_try in (11, 12, 13, 14, 15, 16):
    sat, ww = solve(w_try, dangerous=True, nontrivial=True, s_constraint='nonzero')
    print(f"  dangerous & s!=0, w<={w_try:2d} : SAT={sat}" + (f" (w={ww})" if sat else ""))
    if sat:
        print(f"\n  => minimum-weight s!=0 dangerous logical has weight {ww}.")
        if ww <= 12:
            print("     HARD CASE BINDS THE MINIMUM: a weight-12 s!=0 member exists.")
        else:
            print("     s!=0 is OFF-MINIMUM (>12): easy s=0 case carries the bound. De-risked.")
        break
else:
    print("\n  => UNSAT through w<=16: no light s!=0 member found in range.")
