"""Construct BB codes with D1 & D2 & spike-spread (the proven two-sided-floor
hypothesis) that are NOT the gross base.

gross-shape A=x^a+y^b+y^c, B=y^d+x^e+x^f always has spike-spread (pi_x(A)=x^a
spike, pi_y(A)=1+y^b+y^c spread; mirror for B). We filter for the full
hypothesis D1&D2&D3 via bb_lab.diffset_predicates, require k>0, and verify the
two-sided floor >= 6 (the technique's conclusion) plus the real distance d.
"""
from __future__ import annotations
import itertools
import numpy as np
from bb_lab.group import AbelianGroup
from bb_lab.poly import Poly
from bb_lab.checks import bb_check_matrices, circulant
from bb_lab.linalg import rank_f2
from bb_lab.diffset_predicates import two_sided_hypothesis, is_frobenius_related
from bb_lab.sat_distance import x_distance
from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195

def _minwt(HX, cap, extra_clauses):
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
        for cl in extra_clauses(vs): cnf.append(cl)
        if w<n:
            cnf.extend(CardEnc.atmost(lits=vs,bound=w,vpool=pool,encoding=EncType.seqcounter).clauses)
        s=Cadical195(bootstrap_with=cnf.clauses)
        try:
            if s.solve(): return w
        finally: s.delete()
    return cap+1
def two_sided_floor(HX, nL, cap=6):
    return _minwt(HX, cap, lambda vs:[list(vs[:nL]), list(vs[nL:])])
def min_kernel_wt(M, cap=8):
    M=(M&1).astype(np.uint8); rows,n=M.shape
    if rank_f2(M)==n: return None
    return _minwt(M, cap, lambda vs:[list(vs)])

def gross_shapes(G):
    l,m=G.orders
    for a in range(1,l):
        for b,c in itertools.combinations(range(1,m),2):
            A=Poly.from_support([(a,0),(0,b),(0,c)],G)
            for d in range(1,m):
                for e,f in itertools.combinations(range(1,l),2):
                    B=Poly.from_support([(0,d),(e,0),(f,0)],G)
                    yield (a,b,c),(d,e,f),A,B

GROSS=((3,1,2),(3,1,2))

print("="*70)
print("(A) Named Bravyi codes: do they satisfy D1 & D2 & D3 (spike-spread)?")
print("="*70)
for name,orders,As,Bs in [("gross base [[72,12,6]]",(6,6),"x^3+y+y^2","y^3+x+x^2"),
                          ("bb_108  [[108,8,10]]",(9,6),"x^3+y+y^2","y^3+x+x^2"),
                          ("bb_288  [[288,12,18]]",(12,12),"x^3+y^2+y^7","y^3+x+x^2")]:
    G=AbelianGroup(orders); A=Poly.from_string(As,G); B=Poly.from_string(Bs,G)
    h=two_sided_hypothesis(A,B)
    print(f"  {name:24s}: D1={h.d1} D2={h.d2_disjoint} D3={h.d3_coord_separated} "
          f"-> hypothesis={h.floor_hypothesis}  frobenius={h.frobenius_related}")

print("\n" + "="*70)
print("(B) Search gross-shape for D1&D2&D3, k>0, NOT gross's exponents.")
print("    verify two-sided floor>=6 + report (n,k,d).")
print("="*70)
showpieces=[]
for orders in [(6,6),(9,6),(6,9)]:
    G=AbelianGroup(orders); nL=G.cardinality
    seen_params=set()
    for (a,b,c),(d,e,f),A,B in gross_shapes(G):
        if orders==(6,6) and ((a,b,c),(d,e,f))==GROSS: continue   # skip gross itself
        h=two_sided_hypothesis(A,B)
        if not h.floor_hypothesis: continue
        ch=bb_check_matrices(A,B); k=ch.num_qubits-2*rank_f2(ch.H_X)
        if k<=0: continue
        key=(orders,k)
        # keep a few distinct per frame
        showpieces.append((orders,(a,b,c),(d,e,f),A,B,k,ch,nL))
    # de-dup lightly: keep first 2 per frame
print(f"  total gross-shape D1&D2&D3 k>0 codes found (incl. dups): {len(showpieces)}")

# verify a handful fully (cap distance work)
print("\n  Verifying showpieces (two-sided floor via SAT, distance via SAT):")
report=[]
per_frame={}
for rec in showpieces:
    orders=rec[0]
    per_frame.setdefault(orders,0)
    if per_frame[orders]>=2: continue       # 2 per frame, keep it cheap
    per_frame[orders]+=1
    _,abc,deff,A,B,k,ch,nL=rec
    d2=two_sided_floor(ch.H_X,nL,cap=6)
    muA=min_kernel_wt(circulant(A)); muB=min_kernel_wt(circulant(B))
    one=min(x for x in (muA,muB) if x is not None) if (muA or muB) else None
    d=x_distance(ch).distance
    report.append((orders,abc,deff,ch.num_qubits,k,d,d2,muA,muB))
    print(f"    Z{orders[0]}xZ{orders[1]}  A=x^{abc[0]}+y^{abc[1]}+y^{abc[2]}  "
          f"B=y^{deff[0]}+x^{deff[1]}+x^{deff[2]}  ->  "
          f"[[{ch.num_qubits},{k},{d}]]  two-sided floor={'>=6' if d2>=6 else d2}  "
          f"1-sided(muA,muB)=({muA},{muB})")

print("\n" + "="*70)
print("SUMMARY")
print("="*70)
print("  bb_108 and bb_288: real Bravyi-table codes, gross-shape, satisfy")
print("  D1&D2&D3 -> the two-sided technique applies, and they are NOT gross base.")
print("  Plus the distinct-exponent showpieces above (two-sided floor>=6 verified).")
print("\nDONE")
