"""A15 near-kernel classification, step 7: EXACT t = 3 generalized-window
verification for the |b| = 10 near-kernel class (the full-dispatch W+(t=3)
verdict used a single-extension probe, necessary but not sufficient).

Condition verified per translate: for the min-poke preimage f0 and
W = supp b u seam(f0), every base 1-cycle supported in W u E is a
boundary, for EVERY extra set E of at most t - 1 = 2 cells (empty,
singles, and all ~C(140,2) pairs of non-W cells; rank identity per
window).  This is exactly the hypothesis of the prospective
`dangerous_bound_of_window_general` rung at t = 3.

Usage: uv run python scripts/a15_f2a6_t3_exact.py
"""

import json
import sys
from pathlib import Path

import numpy as np

LAB = Path(__file__).resolve().parent.parent

sys.path.insert(0, str(LAB / "src"))
from bb_lab.group import AbelianGroup
from bb_lab.poly import Poly
from bb_lab.checks import circulant
from bb_lab.linalg import nullspace_f2, rank_f2, rref_f2
import itertools, time

A_STR, B_STR = "1 + y + x", "x*y^6 + x*y^10 + x^2*y^12"
ELL, M = 5, 15
Gb = AbelianGroup((ELL, M)); nb = Gb.cardinality
Gc = AbelianGroup((ELL, 2*M)); nc = Gc.cardinality
elems_b = list(Gb); base_idx = {g:i for i,g in enumerate(Gb)}
cover_idx = {g:i for i,g in enumerate(Gc)}
Ab, Bb = Poly.from_string(A_STR, Gb), Poly.from_string(B_STR, Gb)
Ac = Poly.from_support(Ab.support, Gc); Bc = Poly.from_support(Bb.support, Gc)
MAb, MBb = circulant(Ab).astype(np.uint8), circulant(Bb).astype(np.uint8)
MAc, MBc = circulant(Ac).astype(np.uint8), circulant(Bc).astype(np.uint8)
D2b = np.vstack([MAb, MBb]) % 2; D1b = np.hstack([MBb, MAb]) % 2
D2c = np.vstack([MAc, MBc]) % 2
kerb = nullspace_f2(D2b).astype(np.uint8)
ker_elems = []
for mask in range(16):
    z = np.zeros(nb, dtype=np.uint8)
    for i in range(4):
        if (mask>>i)&1: z ^= kerb[i]
    ker_elems.append(z)
LIFT = np.zeros((nc, nb), dtype=np.uint8)
for i,(x,y) in enumerate(elems_b): LIFT[cover_idx[(x,y)], i] = 1
D2CL = (D2c @ LIFT) % 2

def solve_f2(Amat,b):
    aug = np.hstack([Amat.astype(np.uint8)%2, (b.astype(np.uint8)%2)[:,None]])
    R,piv = rref_f2(aug); ncols = Amat.shape[1]
    if ncols in piv: return None
    x = np.zeros(ncols,dtype=np.uint8)
    for r,c in enumerate(piv): x[c]=R[r,ncols]
    return x

def seam_of(f):
    L = (D2CL @ f)%2
    s = np.zeros(2*nb,dtype=np.uint8)
    for blk in range(2):
        for h in elems_b:
            s[blk*nb+base_idx[h]] = L[blk*nc+cover_idx[(h[0],h[1])]]
    return s

def window_ok(Wm):
    idx = np.nonzero(Wm)[0]
    dim_cyc = len(idx) - rank_f2(D1b[:, idx].T)
    cidx = np.nonzero(1-Wm)[0]
    dim_pre = nb - rank_f2(D2b[cidx,:].T)
    return dim_cyc == dim_pre - 4

d = json.load(open(LAB/"data/a15/f2a6_full_dispatch.json"))
recs = [json.loads(l) for l in open(LAB/"data/a15/f2a6_light_classes.jsonl") if "b_support" in l]
t3 = [c for c in d["classes"] if "W+(t=3)" in c["verdicts"]]
print(f"t=3 classes: {len(t3)}")
TRANS = []
for tx in range(ELL):
    for ty in range(M):
        perm = np.zeros(2*nb, dtype=np.int64)
        for i,(gx,gy) in enumerate(elems_b):
            j = base_idx[((gx+tx)%ELL,(gy+ty)%M)]
            perm[i]=j; perm[nb+i]=nb+j
        TRANS.append(perm)
t0=time.time()
for c in t3:
    r = recs[c["class"]]
    b0 = np.zeros(2*nb,dtype=np.uint8)
    for blk,gx,gy in r["b_support"]: b0[blk*nb+base_idx[(gx,gy)]]=1
    all_ok = True
    for perm in TRANS:
        tb = np.zeros_like(b0); tb[perm]=b0
        f = solve_f2(D2b, tb)
        best=None
        for z in ker_elems:
            fz=(f^z)%2; s=seam_of(fz)
            p=int((s&(1-tb)).sum())
            if best is None or p<best[0]: best=(p,fz,s)
        _,fz,s = best
        W=(tb|s)%2
        nonW = np.nonzero(1-W)[0]
        ok = window_ok(W) and all(window_ok(W | np.eye(2*nb,dtype=np.uint8)[e]) for e in nonW)
        if ok:
            for e1i in range(len(nonW)):
                We1 = W.copy(); We1[nonW[e1i]]=1
                for e2 in nonW[e1i+1:]:
                    Wm = We1.copy(); Wm[e2]=1
                    if not window_ok(Wm):
                        ok=False; break
                if not ok: break
        if not ok:
            all_ok=False
            print(f"  FAIL at translate (class {c['class']})")
            break
    print(f"class {c['class']} (|b|=10, t=3): exact <=2-extension windows "
          f"{'ALL PASS' if all_ok else 'FAIL'} [{time.time()-t0:.0f}s]")
