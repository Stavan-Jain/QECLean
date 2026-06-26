"""Verify the Frobenius counterexample A=B^2 and locate the right hypothesis.

(1) Is the weight-4 cycle (1,B) real in the actual code? logical or stabilizer?
    what is mu_Z (min cycle weight) and k?
(2) Does the Frobenius counterexample violate D3 (coordinate separation),
    while gross satisfies it?
(3) Corrected conjecture: does D1 & D2 & D3 => two-sided cycle floor >= 6
    hold over GENERAL weight-3 (A,B) (not just gross-shape)?  SAT-checked.
"""
from __future__ import annotations
import itertools
import numpy as np
from bb_lab.group import AbelianGroup
from bb_lab.poly import Poly
from bb_lab.checks import bb_check_matrices
from bb_lab.linalg import rank_f2
from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195

def diffset(S, G): return {G.sub(g,h) for g in S for h in S if g!=h}
def is_sidon(S, G):
    d=[G.sub(g,h) for g in S for h in S if g!=h]; return len(d)==len(set(d))
def D3(A,B,G):
    dA,dB=diffset(A.support,G),diffset(B.support,G)
    xsep={d[0] for d in dA}.isdisjoint({d[0] for d in dB})
    ysep={d[1] for d in dA}.isdisjoint({d[1] for d in dB})
    return xsep and ysep
def in_rowspace(M,x):
    return rank_f2(np.vstack([M, x[None,:]&1]))==rank_f2(M)

def min_cycle(HX, cap=7, twosided=False, nL=None):
    HX=(HX&1).astype(np.uint8); rows,n=HX.shape
    for w in range(1,cap+1):
        pool=IDPool(); vs=[pool.id() for _ in range(n)]; cnf=CNF()
        for r in range(rows):
            idx=np.flatnonzero(HX[r])
            if idx.size==0: continue
            acc=vs[idx[0]]
            for i in idx[1:]:
                nw=pool.id(); x=vs[i]
                cnf.append([-nw,-acc,-x]);cnf.append([-nw,acc,x])
                cnf.append([nw,-acc,x]);cnf.append([nw,acc,-x]); acc=nw
            cnf.append([-acc])
        if twosided:
            cnf.append(list(vs[:nL])); cnf.append(list(vs[nL:]))
        else:
            cnf.append(list(vs))
        if w<n:
            cnf.extend(CardEnc.atmost(lits=vs,bound=w,vpool=pool,encoding=EncType.seqcounter).clauses)
        s=Cadical195(bootstrap_with=cnf.clauses)
        try:
            if s.solve(): return w
        finally: s.delete()
    return cap+1

print("="*68)
print("(1) Is the Frobenius weight-4 cycle real?  A=1+x^2+y^2, B=1+x+y")
print("="*68)
for orders in [(5,5),(7,7),(9,6)]:
    G=AbelianGroup(orders); nL=G.cardinality
    A=Poly.from_string("1 + x^2 + y^2",G); B=Poly.from_string("1 + x + y",G)
    ch=bb_check_matrices(A,B); n=ch.num_qubits
    k=n-2*rank_f2(ch.H_X)
    # build v=(delta0, supp B)
    v=np.zeros(n,dtype=np.uint8); v[G.index((0,0))]=1
    for g in B.support: v[nL+G.index(g)]=1
    is_cyc = not ((ch.H_X@v)%2).any()
    is_stab = in_rowspace(ch.H_Z, v)
    muZ = min_cycle(ch.H_X)             # min nonzero cycle weight (stab or logical)
    d2  = min_cycle(ch.H_X, twosided=True, nL=nL)
    print(f"  Z{orders[0]}xZ{orders[1]}: n={n} k={k}  | (1,B) wt={int(v.sum())} "
          f"cycle={is_cyc} stabilizer={is_stab}  | mu_Z(min cycle)={muZ}  two-sided floor d2={d2}")

print("\n  gross base (for contrast):")
G=AbelianGroup((6,6))
gA=Poly.from_string("x^3+y+y^2",G); gB=Poly.from_string("y^3+x+x^2",G)
chg=bb_check_matrices(gA,gB)
print(f"     mu_Z(min cycle)={min_cycle(chg.H_X)}   d2={min_cycle(chg.H_X,twosided=True,nL=36)}")

print("\n" + "="*68)
print("(2) Does D3 (coordinate separation) distinguish them?")
print("="*68)
G=AbelianGroup((6,6))
fA=Poly.from_string("1+x^2+y^2",G); fB=Poly.from_string("1+x+y",G)
print(f"  Frobenius A=B^2 : D1(A,B Sidon)={is_sidon(fA.support,G) and is_sidon(fB.support,G)} "
      f" D2={diffset(fA.support,G).isdisjoint(diffset(fB.support,G))}  D3={D3(fA,fB,G)}")
print(f"  gross          : D3={D3(gA,gB,G)}")

print("\n" + "="*68)
print("(3) Corrected conjecture: D1 & D2 & D3 => d2>=6  over GENERAL weight-3 (A,B)")
print("    (SAT-checked; searches ALL split types, not just (1,w))")
print("="*68)
def weight3_polys(G):
    z=tuple(0 for _ in G.orders); nz=[g for g in G if g!=z]
    out=[]
    for two in itertools.combinations(nz,2):
        S={z,*two}
        if is_sidon(S,G): out.append(S)     # D1 per-polynomial
    return out
for orders in [(5,5),(7,7),(6,6)]:
    G=AbelianGroup(orders); nL=G.cardinality
    polys=weight3_polys(G)
    n_pred=0; viol=[]; checked=0
    for SA in polys:
        dA=diffset(SA,G)
        for SB in polys:
            dB=diffset(SB,G)
            if not dA.isdisjoint(dB): continue            # D2
            A=Poly.from_support(SA,G); B=Poly.from_support(SB,G)
            if not D3(A,B,G): continue                     # D3
            n_pred+=1
            if n_pred>4000: break
            d2=min_cycle(bb_check_matrices(A,B).H_X, cap=6, twosided=True, nL=nL)
            checked+=1
            if d2<6: viol.append((A.canonical_string(),B.canonical_string(),d2))
        else: continue
        break
    print(f"  Z{orders[0]}xZ{orders[1]}: D1&D2&D3 holds for {n_pred} pairs "
          f"(checked {checked}); d2<6 violations: {len(viol)}")
    for v in viol[:4]: print("      VIOLATION:", v)
print("\nDONE")
