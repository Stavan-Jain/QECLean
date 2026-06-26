"""Empirical map of the CRT/F4 engine-half over its group frame.

The engine-half of Theorem A (the one-sided splits) claims: a nonzero element of
Ann(A) = ker(M_A) has weight >= 6, because on the F4 layer frame a nonzero
annihilator must activate a radical component (co-point-or-full) spanning >= 3
even-weight layers. This sweep tests that claim as ground truth:

  TIER 1  every weight-3 polynomial P on Z6^2: exact min nonzero weight mu(P) of
          Ann(P), plus its 5-component CRT/F4 profile -> does mu>=6, and why/why not.
  TIER 2  gross-shape codes A=x^a+y^b+y^c, B=y^d+x^e+x^f on Z6^2 with k>0:
          mu_A, mu_B, exact distance d -> is d realized one-sided (=min(mu_A,mu_B))
          or does a two-sided logical beat it (engine-half blind)?
  TIER 3  real anchors across frames (gross base on Z6^2; [[36,4,4]] on Z3xZ6;
          bb_108 on Z9xZ6 = F64 frame; bb_90 on Z15xZ3 = F16 frame).
"""
from __future__ import annotations
import itertools, collections
import numpy as np

from bb_lab.group import AbelianGroup
from bb_lab.poly import Poly
from bb_lab.checks import bb_check_matrices, circulant
from bb_lab.codeparams import code_params
from bb_lab.linalg import rank_f2
from bb_lab.sat_distance import x_distance
from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195


# ---- exact min nonzero weight of ker(M) over F2, capped (None = trivial kernel)
def min_weight_kernel(M, cap=8):
    M = (M & 1).astype(np.uint8)
    rows, n = M.shape
    if rank_f2(M) == n:
        return None
    for w in range(1, cap + 1):
        pool = IDPool(); vs = [pool.id() for _ in range(n)]; cnf = CNF()
        for r in range(rows):
            idx = np.flatnonzero(M[r])
            if idx.size == 0: continue
            acc = vs[idx[0]]
            for i in idx[1:]:
                nw = pool.id(); x = vs[i]
                cnf.append([-nw,-acc,-x]); cnf.append([-nw,acc,x])
                cnf.append([nw,-acc,x]);  cnf.append([nw,acc,-x]); acc = nw
            cnf.append([-acc])
        cnf.append(list(vs))                      # nonzero
        if w < n:
            cnf.extend(CardEnc.atmost(lits=vs, bound=w, vpool=pool,
                                      encoding=EncType.seqcounter).clauses)
        s = Cadical195(bootstrap_with=cnf.clauses)
        try:
            if s.solve(): return w
        finally:
            s.delete()
    return cap + 1                                 # ">cap"

_muP = {}
def muP(P: Poly):
    key = (P.group.orders, frozenset(P.support))
    if key not in _muP:
        _muP[key] = min_weight_kernel(circulant(P))
    return _muP[key]


# ---- F4 = F2[w]/(w^2+w+1), elements 0,1,2,3 = 0,1,w,w^2 ; add = XOR
def f4_mul(a, b):
    # (a0+a1 w)(b0+b1 w) = (a0b0+a1b1) + (a0b1+a1b0+a1b1) w
    a0,a1 = a&1,(a>>1)&1; b0,b1 = b&1,(b>>1)&1
    lo = (a0*b0 + a1*b1) & 1
    hi = (a0*b1 + a1*b0 + a1*b1) & 1
    return lo | (hi<<1)
W_POW = [1, 2, 3]                                  # w^0=1,(0,1)=2? fix: 1->(1,0)=1, w->(0,1)=2, w^2->(1,1)=3
def wpow(e): return [1,2,3][e % 3]

# 4 Frobenius-orbit reps of nontrivial Z3^2 chars + the trivial layer component
ODD_CHARS = {"layer(triv)": (0,0), "L1(0,1)": (0,1), "L2(1,0)": (1,0),
             "L3(1,1)": (1,1), "L4(1,2)": (1,2)}

def f4_profile_Z6(P: Poly):
    """For P over Z6^2, classify each of the 5 CRT components as zero/unit/radical.
    Z6=Z2xZ3 per coord via (g%2, g%3). Component at odd-char psi lives in F4[Z2^2];
    unit iff aug (sum over Z2^2) != 0, radical iff nonzero but aug==0."""
    assert P.group.orders == (6,6)
    out = {}
    for name,(j,k) in ODD_CHARS.items():
        comp = {}                                  # Z2^2 slot -> F4 value
        for (gx,gy) in P.support:
            s = (gx % 2, gy % 2)
            e = (j*(gx % 3) + k*(gy % 3)) % 3
            val = (1 if (j,k)==(0,0) else wpow(e))  # trivial char contributes 1 (F2)
            comp[s] = comp.get(s, 0) ^ val
        nz = {s:v for s,v in comp.items() if v != 0}
        if not nz:
            out[name] = "zero"
        else:
            aug = 0
            for v in nz.values(): aug ^= v
            out[name] = "unit" if aug != 0 else "radical"
    return out

def profile_counts(prof):
    c = collections.Counter(prof.values())
    return f"unit={c['unit']} radical={c['radical']} zero={c['zero']}"


G66 = AbelianGroup((6,6))

print("="*70)
print("TIER 1 — every weight-3 P on Z6^2 (mod translation, 1 in support)")
print("        engine claims mu(Ann P) >= 6.  Ground truth:")
print("="*70)
pts = [g for g in G66 if g != (0,0)]
hist = collections.Counter()
exceptions = []   # mu < 6
gross_like = []
for two in itertools.combinations(pts, 2):
    supp = frozenset([(0,0), *two])
    P = Poly.from_support(supp, G66)
    m = muP(P)
    label = "trivial-ker" if m is None else (f">{8}" if m == 9 else str(m))
    hist[label] += 1
    if m is not None and m < 6:
        exceptions.append((supp, m))
n_total = sum(hist.values())
print(f"\n  weight-3 polynomials tried: {n_total}")
print("  mu(Ann P) histogram:")
for key in sorted(hist, key=lambda s: (s=="trivial-ker", s)):
    print(f"     mu = {key:>12s} : {hist[key]:4d}")
ge6 = sum(v for k,v in hist.items() if k not in ("trivial-ker",) and (k.startswith(">") or int(k)>=6))
lt6 = sum(v for k,v in hist.items() if k not in ("trivial-ker",) and not (k.startswith(">")) and int(k)<6)
print(f"\n  with a nonzero annihilator: mu>=6 (engine territory): {ge6}"
      f"   mu<6 (engine FAILS): {lt6}")

# profile correlation: sample a few exceptions + gross's A
print("\n  WHY exceptions fail — F4 component profile (sample):")
for supp, m in exceptions[:6]:
    prof = f4_profile_Z6(Poly.from_support(supp, G66))
    print(f"     mu={m}  supp={sorted(supp)}  -> {profile_counts(prof)}")
grossA = Poly.from_string("x^3 + y + y^2", G66)
grossB = Poly.from_string("y^3 + x + x^2", G66)
print("\n  gross A profile:", profile_counts(f4_profile_Z6(grossA)),
      " mu_A =", muP(grossA), " detail:", f4_profile_Z6(grossA))
print("  gross B profile:", profile_counts(f4_profile_Z6(grossB)),
      " mu_B =", muP(grossB))


print("\n" + "="*70)
print("TIER 2 — gross-shape codes on Z6^2:  A=x^a+y^b+y^c, B=y^d+x^e+x^f, k>0")
print("="*70)
def shapeA(a,b,c): return Poly.from_support([(a,0),(0,b),(0,c)], G66)
def shapeB(d,e,f): return Poly.from_support([(0,d),(e,0),(f,0)], G66)
As = [(a,b,c) for a in range(1,6) for b,c in itertools.combinations(range(1,6),2)]
Bs = [(d,e,f) for d in range(1,6) for e,f in itertools.combinations(range(1,6),2)]
codes = []
for (a,b,c) in As:
    A = shapeA(a,b,c)
    for (d,e,f) in Bs:
        B = shapeB(d,e,f)
        ch = bb_check_matrices(A,B)
        n = ch.num_qubits; rX = rank_f2(ch.H_X)
        k = n - 2*rX
        if k > 0:
            codes.append(((a,b,c),(d,e,f),A,B,k))
print(f"  gross-shape pairs: {len(As)*len(Bs)}   with k>0: {len(codes)}")

# dedupe by (k, mu_A, mu_B) signature is too coarse; cap exact-d work
buckets = collections.Counter()   # classification
dhist = collections.Counter(); floorhist = collections.Counter()
rows = []
for i in range(len(codes)):        # ALL k>0 gross-shape codes (no sampling bias)
    (a,b,c),(d,e,f),A,B,k = codes[i]
    mA, mB = muP(A), muP(B)
    ch = bb_check_matrices(A,B)
    dd = x_distance(ch).distance
    floor = min(x for x in (mA,mB) if x is not None) if (mA or mB) else None
    if floor is None:
        cls = "no-annihilator"
    elif dd < floor:
        cls = "two-sided<one-sided"
    elif dd == floor:
        cls = "one-sided tight"
    else:
        cls = "one-sided is stabilizer (d>floor)"
    buckets[cls]+=1; dhist[dd]+=1
    if floor is not None: floorhist[min(floor,9)]+=1
    rows.append((k,dd,mA,mB,cls,(a,b,c),(d,e,f)))
print(f"\n  exact d computed for ALL {len(rows)} k>0 codes. classification:")
for cls,ct in buckets.most_common():
    print(f"     {cls:34s}: {ct}  ({100*ct/len(rows):.0f}%)")
print("  distance d histogram:", dict(sorted(dhist.items())))
print("  one-sided floor min(mu_A,mu_B) histogram (9 = >8):", dict(sorted(floorhist.items())))
# show gross base if present
print("\n  sample rows [k, d, mu_A, mu_B, class,  A-shape, B-shape]:")
for r in rows[:14]:
    print("    ", r)
# explicit gross base
gb = bb_check_matrices(grossA, grossB)
print("\n  >> gross base [[72,12,?]] check:",
      "k=", gb.num_qubits-2*rank_f2(gb.H_X),
      " d=", x_distance(gb).distance, " mu_A=", muP(grossA), " mu_B=", muP(grossB))


print("\n" + "="*70)
print("TIER 3 — real anchors across frames (mu via SAT; d from Bravyi table)")
print("="*70)
anchors = [
    ("gross base [[72,12,6]]",  (6,6),  "x^3 + y + y^2", "y^3 + x + x^2", 6,  "Z2^2 x Z3^2  (F4 frame, 4 slots)"),
    ("[[36,4,4]] base",         (3,6),  "x^2 + y + y^3", "1 + x + y^2",   4,  "Z2 x Z3^2    (F4 frame, 2 slots)"),
    ("bb_108 [[108,8,10]]",     (9,6),  "x^3 + y + y^2", "y^3 + x + x^2", 10, "Z9 x Z2 x Z3 (Z9 -> F64 frame)"),
    ("bb_90 [[90,8,10]]",       (15,3), "x^9 + y + y^2", "1 + x^2 + x^7", 10, "Z5 x Z3^2    (Z5 -> F16 frame)"),
]
print(f"\n  {'code':26s} {'group':9s} {'mu_A':>5s} {'mu_B':>5s} {'d':>3s}   frame")
for name,(l,m),As_,Bs_,d_known,frame in anchors:
    G = AbelianGroup((l,m))
    A = Poly.from_string(As_, G); B = Poly.from_string(Bs_, G)
    mA, mB = muP(A), muP(B)
    fa = "triv" if mA is None else (">8" if mA==9 else mA)
    fb = "triv" if mB is None else (">8" if mB==9 else mB)
    print(f"  {name:26s} Z{l}xZ{m:<5d} {str(fa):>5s} {str(fb):>5s} {d_known:>3d}   {frame}")

print("\nDONE")
