"""Try to PROVE  D1 & D2  =>  two-sided cycle floor >= 2w  (w=|supp A|=|supp B|).

Proof sketch reduces the whole claim to: can a (1,w) two-sided cycle exist under
D1&D2?  i.e. is there a Sidon A and Sidon B with dA ∩ dB = ∅ and a weight-w
u_R with  A = B·u_R  (so (δ0, u_R) is a weight-(1+w) two-sided cycle < 2w)?

We CONSTRUCT-search for exactly this across frames.  If found, the general
conjecture is FALSE and we report the counterexample + what extra hypothesis
the gross proof's D3 supplies.
"""
from __future__ import annotations
import itertools
import numpy as np
from bb_lab.group import AbelianGroup
from bb_lab.poly import Poly
from bb_lab.checks import bb_check_matrices
from bb_lab.linalg import rank_f2

def diffs(S, G):
    return [G.sub(g, h) for g in S for h in S if g != h]
def diffset(S, G):
    return set(diffs(S, G))
def is_sidon(S, G):
    d = diffs(S, G)
    return len(d) == len(set(d))          # all w(w-1) differences distinct (ov<=1)
def conv_set(Bsupp, uR, G):
    """support of B·u_R over F2 = symmetric difference of translates."""
    acc = set()
    for r in uR:
        for b in Bsupp:
            c = G.add(b, r)
            acc ^= {c}
    return acc

def search_frame(orders, w=3, max_report=3):
    G = AbelianGroup(orders); elems = list(G); zero = tuple(0 for _ in orders)
    nonzero = [g for g in elems if g != zero]
    found = []
    # B: Sidon w-set containing 0 (translation gauge)
    for rest in itertools.combinations(nonzero, w-1):
        Bsupp = {zero, *rest}
        if not is_sidon(Bsupp, G):
            continue
        dB = diffset(Bsupp, G)
        # u_R: a "dB-(w)-clique": w points (0 + w-1 offsets) pairwise differing by dB
        # build offsets o_2..o_w in dB with all pairwise diffs in dB
        cand = [d for d in dB]
        for combo in itertools.combinations(cand, w-1):
            uR = (zero, *combo)
            if len(set(uR)) != w:
                continue
            ok = all(G.sub(p, q) in dB for p in uR for q in uR if p != q)
            if not ok:
                continue
            sigma = conv_set(Bsupp, uR, G)
            if len(sigma) != w:          # need |σ| = w  (a single A-translate)
                continue
            if not is_sidon(sigma, G):   # A = σ must be Sidon (D1 for A)
                continue
            dA = diffset(sigma, G)
            if dA.isdisjoint(dB):        # D2 holds
                found.append((Bsupp, uR, frozenset(sigma)))
                if len(found) >= max_report:
                    return G, found
    return G, found

print("="*70)
print("Counterexample search:  D1&D2 with a weight-(1+w) two-sided cycle?")
print("="*70)
for orders in [(6,6),(7,7),(8,8),(5,5),(10,10),(6,12),(9,6),(12,6)]:
    G, found = search_frame(orders, w=3)
    tag = f"Z{orders[0]}xZ{orders[1]}"
    if found:
        print(f"\n{tag}: FOUND {len(found)} (1,3) counterexample(s) under D1&D2:")
        for Bsupp, uR, sigma in found[:2]:
            A = Poly.from_support(sigma, G); B = Poly.from_support(Bsupp, G)
            # rigorous check via the actual code: is there a weight-4 two-sided cycle?
            ch = bb_check_matrices(A, B)
            print(f"   A=supp{sorted(sigma)}  B=supp{sorted(Bsupp)}  u_R={sorted(uR)}")
            print(f"       A canon: {A.canonical_string()}")
            print(f"       B canon: {B.canonical_string()}")
            # verify A·δ0 == B·u_R as sets:
            lhs = set(sigma)
            rhs = conv_set(Bsupp, uR, G)
            print(f"       check  A == B·u_R : {lhs == rhs}   (=> (δ0,u_R) is a wt-{1+len(uR)} two-sided cycle)")
            dA = diffset(sigma, G); dB = diffset(Bsupp, G)
            print(f"       D1(A Sidon)={is_sidon(sigma,G)}  D1(B Sidon)={is_sidon(Bsupp,G)}  D2(dA∩dB=∅)={dA.isdisjoint(dB)}")
            # the 2nd-order quantity the gap lives in:
            dBdB = {G.sub(x,y) for x in dB for y in dB}
            inter = dA & dBdB
            print(f"       dA ∩ (dB−dB) = {sorted(inter)[:6]}{'...' if len(inter)>6 else ''}  (size {len(inter)}) -- the gap")
    else:
        print(f"\n{tag}: no (1,3) counterexample found.")
print("\nDONE")
