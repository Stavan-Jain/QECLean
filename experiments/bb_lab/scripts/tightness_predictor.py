"""Is the 2w floor tight or loose? Test an ANALYTIC predictor.

Hypothesis: tightness is controlled by the annihilator minimum weight.
  mu_A = min nonzero weight in Ann(A) = ker(M_A)  [one-sided logical source]
  mu_A = d_G(Z(A)): min Hamming weight with Fourier support in A's zero-set
         (the generalized layer dictionary / a BCH-uncertainty bound).
Predictor:  d(base) = 2w  (TIGHT)   iff   min(mu_A, mu_B) = 2w.
Cheap proxy: dim ker(M_A) = |G| - rank(M_A) (size of A's zero-set); large
kernel => low-weight annihilator => tight.

Tested over gross-shape D1&D2&D3 codes (where the floor >= 2w holds) on
several frames, with d, mu_A, mu_B all SAT/exact.
"""
from __future__ import annotations
import itertools, collections
import numpy as np
from bb_lab.group import AbelianGroup
from bb_lab.poly import Poly
from bb_lab.checks import bb_check_matrices, circulant
from bb_lab.linalg import rank_f2
from bb_lab.diffset_predicates import two_sided_hypothesis
from bb_lab.sat_distance import x_distance
from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195

def _minwt(M, cap, extra):
    M=(M&1).astype(np.uint8); rows,n=M.shape
    for w in range(1,cap+1):
        pool=IDPool(); vs=[pool.id() for _ in range(n)]; cnf=CNF()
        for r in range(rows):
            idx=np.flatnonzero(M[r])
            if idx.size==0: continue
            acc=vs[idx[0]]
            for i in idx[1:]:
                nw=pool.id(); x=vs[i]
                cnf.append([-nw,-acc,-x]);cnf.append([-nw,acc,x])
                cnf.append([nw,-acc,x]);cnf.append([nw,acc,-x]); acc=nw
            cnf.append([-acc])
        for cl in extra(vs): cnf.append(cl)
        if w<n:
            cnf.extend(CardEnc.atmost(lits=vs,bound=w,vpool=pool,encoding=EncType.seqcounter).clauses)
        s=Cadical195(bootstrap_with=cnf.clauses)
        try:
            if s.solve(): return w
        finally: s.delete()
    return cap+1

_mu={}
def mu_ann(P, cap=10):
    key=(P.group.orders, frozenset(P.support))
    if key in _mu: return _mu[key]
    M=circulant(P)
    val = None if rank_f2(M)==M.shape[1] else _minwt(M,cap,lambda vs:[list(vs)])
    _mu[key]=val; return val
def dim_ker(P):
    M=circulant(P); return M.shape[1]-rank_f2(M)

def gross_shapes(G):
    l,m=G.orders
    for a in range(1,l):
        for b,c in itertools.combinations(range(1,m),2):
            A=Poly.from_support([(a,0),(0,b),(0,c)],G)
            for d in range(1,m):
                for e,f in itertools.combinations(range(1,l),2):
                    B=Poly.from_support([(0,d),(e,0),(f,0)],G)
                    yield A,B

W=3; TWO_W=6
print("="*78)
print(f"Tightness predictor over gross-shape D1&D2&D3 codes (w={W}, 2w={TWO_W})")
print(f"{'frame':8s} {'[[n,k,d]]':14s} {'d':>3s} {'muA':>4s} {'muB':>4s} {'min_mu':>6s} "
      f"{'dimkerA':>7s} {'tight?':>6s} {'pred(min_mu==6)':>15s} {'agree':>5s}")
rows=[]
per_frame={}
for orders in [(6,6),(9,6),(6,9),(12,6)]:
    G=AbelianGroup(orders)
    for A,B in gross_shapes(G):
        if not two_sided_hypothesis(A,B).floor_hypothesis: continue
        ch=bb_check_matrices(A,B); k=ch.num_qubits-2*rank_f2(ch.H_X)
        if k<=0: continue
        per_frame.setdefault(orders,0)
        if per_frame[orders]>=6: break        # sample up to 6 per frame
        per_frame[orders]+=1
        muA=mu_ann(A); muB=mu_ann(B)
        mn=min(x for x in (muA,muB) if x is not None) if (muA or muB) else 99
        d=x_distance(ch).distance
        tight=(d==TWO_W); pred=(mn==TWO_W); agree=(tight==pred)
        rows.append((orders,ch.num_qubits,k,d,muA,muB,mn,dim_ker(A),tight,pred,agree))
        print(f"Z{orders[0]}xZ{orders[1]:<4d} [[{ch.num_qubits},{k},{d}]]".ljust(23)+
              f"{d:>3d} {str(muA):>4s} {str(muB):>4s} {mn:>6d} {dim_ker(A):>7d} "
              f"{str(tight):>6s} {str(pred):>15s} {('OK' if agree else 'XXX'):>5s}")

print("\n" + "-"*78)
nag=sum(1 for r in rows if r[-1])
print(f"predictor 'tight <=> min(mu_A,mu_B)==2w' agrees on {nag}/{len(rows)} sampled codes")
tl=collections.Counter((r[8],r[9]) for r in rows)   # (tight, pred)
print(f"  confusion (tight, predicted-tight): {dict(tl)}")
# proxy: dim ker vs tight
print("\n  dim ker(M_A) by tightness (proxy: larger kernel => tighter):")
for t in (True,False):
    ks=[r[7] for r in rows if r[8]==t]
    if ks: print(f"     tight={t}: dim ker(M_A) in [{min(ks)},{max(ks)}], mean {sum(ks)/len(ks):.1f}")
print("\nANCHORS:")
for name,orders,As,Bs in [("gross",(6,6),"x^3+y+y^2","y^3+x+x^2"),
                          ("bb_108",(9,6),"x^3+y+y^2","y^3+x+x^2")]:
    G=AbelianGroup(orders);A=Poly.from_string(As,G);B=Poly.from_string(Bs,G)
    ch=bb_check_matrices(A,B)
    print(f"  {name}: d={x_distance(ch).distance} muA={mu_ann(A)} muB={mu_ann(B)} "
          f"dimkerA={dim_ker(A)}")
print("\nDONE")
