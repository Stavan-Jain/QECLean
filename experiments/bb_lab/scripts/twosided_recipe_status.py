"""Status of  D1 & D2 & (spike-spread)  =>  two-sided floor >= 2w.

Q1: the gross PROOF is an instance proof (the (2,2)/(1,3) steps hard-code
    per-polynomial facts). So the parametric statement is a CONJECTURE.
    -> test the conjecture (floor >= 2w) on spike-spread D1&D2 codes across frames.

Q2: the gross argument is a RECIPE whose steps are per-polynomial finite checks.
    One key obligation in the (2,2) sigma=4 sub-case: the spread's 1-variable
    annihilator must have min weight > 2 (so a weight-<=2 element is 0).
    -> compute that obligation for the spreads that actually occur; is it robust?
"""
from __future__ import annotations
import itertools, collections
import numpy as np
from bb_lab.group import AbelianGroup
from bb_lab.poly import Poly
from bb_lab.checks import bb_check_matrices, circulant
from bb_lab.linalg import rank_f2
from bb_lab.diffset_predicates import is_sidon, difference_sets_disjoint, coordinate_separated
from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195

def min_weight_kernel(M, cap=8):
    M=(M&1).astype(np.uint8); rows,n=M.shape
    if rank_f2(M)==n: return None
    for w in range(1,cap+1):
        pool=IDPool(); vs=[pool.id() for _ in range(n)]; cnf=CNF()
        for r in range(rows):
            idx=np.flatnonzero(M[r])
            if idx.size==0: continue
            acc=vs[idx[0]]
            for i in idx[1:]:
                nw=pool.id(); x=vs[i]
                cnf.append([-nw,-acc,-x]);cnf.append([-nw,acc,x]);cnf.append([nw,-acc,x]);cnf.append([nw,acc,-x]);acc=nw
            cnf.append([-acc])
        cnf.append(list(vs))
        if w<n: cnf.extend(CardEnc.atmost(lits=vs,bound=w,vpool=pool,encoding=EncType.seqcounter).clauses)
        s=Cadical195(bootstrap_with=cnf.clauses)
        try:
            if s.solve(): return w
        finally: s.delete()
    return cap+1

def two_sided_floor(HX,nL,cap=7):
    HX=(HX&1).astype(np.uint8); rows,n=HX.shape
    for w in range(2,cap+1):
        pool=IDPool(); vs=[pool.id() for _ in range(n)]; cnf=CNF()
        for r in range(rows):
            idx=np.flatnonzero(HX[r])
            if idx.size==0: continue
            acc=vs[idx[0]]
            for i in idx[1:]:
                nw=pool.id(); x=vs[i]
                cnf.append([-nw,-acc,-x]);cnf.append([-nw,acc,x]);cnf.append([nw,-acc,x]);cnf.append([nw,acc,-x]);acc=nw
            cnf.append([-acc])
        cnf.append(list(vs[:nL])); cnf.append(list(vs[nL:]))
        if w<n: cnf.extend(CardEnc.atmost(lits=vs,bound=w,vpool=pool,encoding=EncType.seqcounter).clauses)
        s=Cadical195(bootstrap_with=cnf.clauses)
        try:
            if s.solve(): return w
        finally: s.delete()
    return cap+1

def ann_min_weight_1d(exps, n):
    """min nonzero annihilator weight of the spread 1 + sum x^e over Z_n."""
    G=AbelianGroup((n,)); P=Poly.from_support([(0,)]+[(e,) for e in exps], G)
    m=min_weight_kernel(circulant(P), cap=6)
    return m   # None = trivial kernel (no annihilator)

# spike-spread gross-shape on Z_l x Z_m:  A = x^a + y^b + y^c ,  B = y^d + x^e + x^f
def sweep(l, m, cap_codes=400):
    G=AbelianGroup((l,m)); nL=G.cardinality; w=3
    As=[(a,b,c) for a in range(1,l) for b,c in itertools.combinations(range(1,m),2)]
    Bs=[(d,e,f) for d in range(1,m) for e,f in itertools.combinations(range(1,l),2)]
    n_codes=0; floor_viol=[]; ann_fail=[]; d2hist=collections.Counter(); checked=0
    for (a,b,c) in As:
        A=Poly.from_support([(a,0),(0,b),(0,c)],G)
        if not is_sidon(A): continue
        for (d,e,f) in Bs:
            B=Poly.from_support([(0,d),(e,0),(f,0)],G)
            if not is_sidon(B): continue
            if not difference_sets_disjoint(A,B): continue       # D2
            ch=bb_check_matrices(A,B); k=ch.num_qubits-2*rank_f2(ch.H_X)
            if k<=0: continue                                     # real codes only
            n_codes+=1
            if n_codes>cap_codes: break
            checked+=1
            d2=two_sided_floor(ch.H_X,nL); d2hist[min(d2,8)]+=1
            if d2<2*w: floor_viol.append((A.canonical_string(),B.canonical_string(),d2))
            # recipe obligation: spreads pi_y(A)=1+y^b+y^c (over Z_m), pi_x(B)=1+x^e+x^f (over Z_l)
            annA=ann_min_weight_1d([b,c], m); annB=ann_min_weight_1d([e,f], l)
            small=[x for x in (annA,annB) if x is not None and x<=2]
            if small: ann_fail.append((A.canonical_string(),B.canonical_string(),annA,annB))
        else: continue
        break
    print(f"\n### Z{l}xZ{m}: {checked} spike-spread D1&D2 k>0 codes (w={w}, target floor {2*w})")
    print(f"   floor>=2w violations: {len(floor_viol)}   d2 hist (8=>=8): {dict(sorted(d2hist.items()))}")
    for v in floor_viol[:4]: print("      FLOOR<2w:", v)
    print(f"   recipe (2,2)-annihilator obligation (spread Ann min wt > 2) FAILS for: {len(ann_fail)} codes")
    for v in ann_fail[:4]: print("      ANN<=2:", v)

print("Q2 grounding: floor robustness + recipe-obligation robustness for spike-spread D1&D2")
for (l,m) in [(6,6),(9,6),(6,12)]:
    sweep(l,m)

# also: are Sidon spreads' annihilators ever light? scan 1+x^e+x^f over Z_n
print("\n--- Sidon 3-term spread annihilator min-weights 1+x^e+x^f over Z_n ---")
for n in [5,6,7,8,9,12]:
    G=AbelianGroup((n,)); vals=collections.Counter(); light=[]
    for e,f in itertools.combinations(range(1,n),2):
        P=Poly.from_support([(0,),(e,),(f,)],G)
        if not is_sidon(P): continue
        m=min_weight_kernel(circulant(P),cap=6)
        key="triv" if m is None else (">6" if m==7 else m)
        vals[key]+=1
        if m is not None and m<=2: light.append((e,f,m))
    print(f"   Z{n}: Sidon-spread ann-minwt hist {dict(vals)}   (<=2: {light[:5]})")
print("\nDONE")
