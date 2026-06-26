"""Independently verify the fork's Z8^2 finding: a Frobenius pair A=B^2 that
satisfies D1&D2&D3 (so floor_hypothesis=True AND frobenius_related=True), with a
weight-4 two-sided cycle => D1&D2&D3 => floor>=2w is FALSE on Z8^2.

Then the forward question: on Z8^2, is D1&D2&D3 & NOT-frobenius_related
sufficient (floor>=6), or do non-Frobenius D1&D2&D3 violations also appear?
"""
from __future__ import annotations
import itertools, collections
import numpy as np
from bb_lab.group import AbelianGroup
from bb_lab.poly import Poly
from bb_lab.checks import bb_check_matrices
from bb_lab.linalg import rank_f2
from bb_lab.diffset_predicates import two_sided_hypothesis, is_frobenius_related, frobenius_square
from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195

def two_sided_floor(HX, nL, cap=6):
    HX=(HX&1).astype(np.uint8); rows,n=HX.shape
    for w in range(2,cap+1):
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
        cnf.append(list(vs[:nL])); cnf.append(list(vs[nL:]))
        if w<n:
            cnf.extend(CardEnc.atmost(lits=vs,bound=w,vpool=pool,encoding=EncType.seqcounter).clauses)
        s=Cadical195(bootstrap_with=cnf.clauses)
        try:
            if s.solve(): return w
        finally: s.delete()
    return cap+1

print("="*72)
print("(1) Reproduce the fork's Z8^2 Frobenius pair through the committed module")
print("="*72)
G=AbelianGroup((8,8))
B=Poly.from_support([(0,0),(1,1),(4,5)], G)
A=frobenius_square(B)
print(f"  B = supp{sorted(B.support)}")
print(f"  A = B^2 = supp{sorted(A.support)}")
h=two_sided_hypothesis(A,B)
ch=bb_check_matrices(A,B); nL=G.cardinality; k=ch.num_qubits-2*rank_f2(ch.H_X)
d2=two_sided_floor(ch.H_X, nL, cap=6)
print(f"  two_sided_hypothesis: D1={h.d1} D2={h.d2_disjoint} D3={h.d3_coord_separated}"
      f" -> floor_hypothesis={h.floor_hypothesis}")
print(f"  is_frobenius_related = {h.frobenius_related}")
print(f"  code [[{ch.num_qubits},{k},?]]   SAT two-sided floor = {d2}   (2w=6)")
print(f"  => D1&D2&D3 => floor>=2w is {'VIOLATED' if d2<6 else 'ok'} on Z8^2")
print(f"  => docstring 'frobenius_related always False when floor_hypothesis' is "
      f"{'FALSE' if (h.floor_hypothesis and h.frobenius_related) else 'ok'}")

print("\n" + "="*72)
print("(2) Forward sweep on Z8^2: is D1&D2&D3 & NOT-frobenius sufficient?")
print("    enumerate wt-3 (A,B) mod translation, filter D1&D2&D3, split by")
print("    frobenius, SAT-check a sample of NON-frobenius for floor<6.")
print("="*72)
z=(0,0); pts=[g for g in G if g!=z]
def sidon(S):
    d=[G.sub(a,b) for a in S for b in S if a!=b]; return len(d)==len(set(d))
# weight-3 polys with 0 in support, Sidon
polys=[]
for two in itertools.combinations(pts,2):
    S=frozenset([z,*two])
    if sidon(S): polys.append(S)
print(f"  Sidon wt-3 polys (mod translation): {len(polys)}")

# To bound: cap A-enumeration; for each A scan all B; filter; SAT non-frob sample.
n_pred=0; n_frob=0; n_nonfrob=0
nonfrob_violations=[]; nonfrob_checked=0; frob_violations=0
CAP_A=120; SAT_CAP=200
import sys
for ai,SA in enumerate(polys[:CAP_A]):
    A=Poly.from_support(SA,G)
    for SB in polys:
        B=Poly.from_support(SB,G)
        h=two_sided_hypothesis(A,B)
        if not h.floor_hypothesis: continue
        n_pred+=1
        if h.frobenius_related:
            n_frob+=1
        else:
            n_nonfrob+=1
            if nonfrob_checked < SAT_CAP:
                ch=bb_check_matrices(A,B)
                d2=two_sided_floor(ch.H_X, G.cardinality, cap=6)
                nonfrob_checked+=1
                if d2<6:
                    nonfrob_violations.append((sorted(SA),sorted(SB),d2))
print(f"  (A-enum capped at {CAP_A}/{len(polys)})")
print(f"  D1&D2&D3 pairs found: {n_pred}   frobenius: {n_frob}   non-frobenius: {n_nonfrob}")
print(f"  non-frobenius SAT-checked: {nonfrob_checked}   floor<6 violations: {len(nonfrob_violations)}")
for v in nonfrob_violations[:8]:
    print("     NON-FROBENIUS VIOLATION:", v)
if not nonfrob_violations and nonfrob_checked>0:
    print("  -> within the sample, D1&D2&D3 & NOT-frobenius had NO floor<6 violation on Z8^2")
print("\nDONE")
