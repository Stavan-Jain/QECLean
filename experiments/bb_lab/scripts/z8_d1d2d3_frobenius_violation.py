import numpy as np
from bb_lab.group import AbelianGroup
from bb_lab.poly import Poly
from bb_lab.checks import bb_check_matrices
from bb_lab.linalg import rank_f2
from bb_lab.diffset_predicates import two_sided_hypothesis, frobenius_square
from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195

def min_twosided(HX,nL,cap=7):
    HX=(HX&1).astype(np.uint8);rows,n=HX.shape
    for w in range(2,cap+1):
        pool=IDPool();vs=[pool.id() for _ in range(n)];cnf=CNF()
        for r in range(rows):
            idx=np.flatnonzero(HX[r])
            if idx.size==0:continue
            acc=vs[idx[0]]
            for i in idx[1:]:
                nw=pool.id();x=vs[i]
                cnf.append([-nw,-acc,-x]);cnf.append([-nw,acc,x]);cnf.append([nw,-acc,x]);cnf.append([nw,acc,-x]);acc=nw
            cnf.append([-acc])
        cnf.append(list(vs[:nL]));cnf.append(list(vs[nL:]))
        if w<n:cnf.extend(CardEnc.atmost(lits=vs,bound=w,vpool=pool,encoding=EncType.seqcounter).clauses)
        s=Cadical195(bootstrap_with=cnf.clauses)
        try:
            if s.solve():return w
        finally:s.delete()
    return cap+1

G=AbelianGroup((8,8)); nL=64
B=Poly.from_support([(0,0),(1,1),(4,5)],G); A=frobenius_square(B)
print("Z8xZ8 Frobenius pair:  B=",sorted(B.support),"  A=B^2=",sorted(A.support))
h=two_sided_hypothesis(A,B)
print(f"  D1={h.d1} D2={h.d2_disjoint} D3={h.d3_coord_separated}  ->  floor_hypothesis(D1&D2&D3)={h.floor_hypothesis}")
print(f"  is_frobenius_related = {h.frobenius_related}   (gate catches it; D3 does NOT)")
ch=bb_check_matrices(A,B); k=ch.num_qubits-2*rank_f2(ch.H_X)
# verify (1,B) is a weight-4 two-sided cycle
v=np.zeros(2*nL,np.uint8); v[G.index((0,0))]=1
for g in B.support: v[nL+G.index(g)]=1
print(f"  (1,B): cycle? {not ((ch.H_X@v)%2).any()}  weight={int(v.sum())}   k={k}")
f=min_twosided(ch.H_X,nL,cap=7)
print(f"  SAT two-sided floor = {f}   (conjecture needs >= 2w = 6)")
print(f"  => D1&D2&D3 ⟹ floor>=6 is {'VIOLATED' if f<6 else 'OK'} on Z8xZ8")
