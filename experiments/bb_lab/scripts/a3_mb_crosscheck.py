"""A3 / Track 1.1 Entry 5/6 — end-to-end crosschecks of the m(b) picture.

C1  The assembled prediction from the scan (a3_mb_scan.py): the b != 0 part of
    the dangerous sector has minimum exactly 14 (worst light-b slice value
    |b| + 2 m(b) = 6 + 8, all other slices >= 14 except heavy-b >= 12...).
    More precisely the scan + heavy-b triviality predict:
        min{|v| : v dangerous nontrivial, p(v) != 0} in {12, 13, 14}
    with 14 iff no heavy-b slice (|b| >= 12) dips below 14. Decide it by
    direct SAT on the cover: UNSAT at w <= 13 => the b != 0 minimum is 14,
    matching the worst light slice; the m(b) ladder then accounts for the
    ENTIRE dangerous sector with the b = 0 slice carrying the global 12.

C2  The im(Delta)-distance of the base code: min weight of a 1-cycle whose
    class is a NONZERO element of im(Delta). T4 found no weight-6 ones
    (all 84 weight-6 logicals are non-imD); compute the exact minimum.
    (Not load-bearing for the lemma; a structural invariant of the Smith
    sequence worth recording: im(Delta) classes are heavier than d_base.)

Discovery/validation only; never load-bearing in a final analytic proof.
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
HXc, HZc = cm_c.H_X & 1, cm_c.H_Z & 1
HXb, HZb = cm_b.H_X & 1, cm_b.H_Z & 1
nc, nb = Gc.cardinality, Gb.cardinality
N, n = 2 * nc, 2 * nb
d2b = HZb.T

def base_of(g): return (g[0] % 6, g[1])

P1 = np.zeros((n, N), np.uint8)
for g in Gc:
    gi, bi = Gc.index(g), Gb.index(base_of(g))
    P1[bi, gi] ^= 1; P1[nb + bi, nc + gi] ^= 1

def d2c_cut0():
    def sheet(g): return 1 if g[0] >= 6 else 0
    row_perm = np.empty(nc, dtype=int); col_perm = np.empty(N, dtype=int)
    for g in Gc:
        gi, bi = Gc.index(g), Gb.index(base_of(g))
        row_perm[gi] = sheet(g) * nb + bi
        for blk in (0, 1):
            col_perm[blk * nc + gi] = sheet(g) * n + blk * nb + bi
    HZc_p = np.zeros_like(HZc); HZc_p[row_perm[:, None], col_perm[None, :]] = HZc
    return HZc_p[:nb, n:].T

ker_d2b = nullspace_f2(d2b)
logXb = quotient_complement_basis(HXb, nullspace_f2(HZb))
logXc = quotient_complement_basis(HXc, nullspace_f2(HZc))
imD_cls = (((d2c_cut0() @ ker_d2b.T).T % 2) @ logXb.T) % 2
mu = nullspace_f2(imD_cls)
eta = (mu @ logXb) % 2

D = np.array([((P1.T @ (g & 1)) % 2) for g in logXb], dtype=np.uint8)

print("=== C1: dangerous nontrivial with p(v) != 0 -- direct cover SAT ===")
def solve_pv_nonzero(weight):
    pool = IDPool(); qv = [pool.id() for _ in range(N)]; cnf = CNF()
    def parity(row):
        return _xor_chain((qv[i] for i in np.flatnonzero(row)), pool, cnf)
    for r in HXc:
        o = parity(r)
        if o is not None: cnf.append([-o])
    for r in D:
        o = parity(r)
        if o is not None: cnf.append([-o])
    outs = [parity(L & 1) for L in logXc]
    cnf.append([o for o in outs if o is not None])
    outs = [parity(r) for r in P1]                       # p(v) != 0
    cnf.append([o for o in outs if o is not None])
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

for w_try in (12, 13, 14):
    sat, ww = solve_pv_nonzero(w_try)
    print(f"  dangerous, nontrivial, p(v)!=0, w<={w_try}: SAT={sat}" + (f" (w={ww})" if sat else ""))
    if sat:
        break
print("  (prediction from scan: UNSAT at 13, SAT at 14 -- worst slice is |b|=6, m=4)")

print("\n=== C2: im(Delta)-distance of the base code ===")
def solve_imD(weight):
    pool = IDPool(); uv = [pool.id() for _ in range(n)]; cnf = CNF()
    def parity(row):
        return _xor_chain((uv[i] for i in np.flatnonzero(row)), pool, cnf)
    for r in HXb:
        o = parity(r)
        if o is not None: cnf.append([-o])
    outs = [parity(g & 1) for g in logXb]                # class != 0
    cnf.append([o for o in outs if o is not None])
    for r in eta:                                        # class in im(Delta)
        o = parity(r)
        if o is not None: cnf.append([-o])
    card = CardEnc.atmost(lits=uv, bound=weight, vpool=pool, encoding=EncType.seqcounter)
    cnf.extend(card.clauses)
    s = Cadical195(bootstrap_with=cnf.clauses)
    sat = s.solve(); s.delete()
    return sat

for w_try in range(6, 13):
    sat = solve_imD(w_try)
    print(f"  im(Delta)-class cycle, w<={w_try}: SAT={sat}")
    if sat:
        print(f"  => im(Delta)-distance = {w_try} (vs d_base = 6)")
        break

print("\nDone.")
