"""A3 / Track 1.1 Entry 8 — CRT layer-dictionary lower bound for the tail.

Frame (Entry 7, validated): G = Z6^2 = Z2^2 x Z3^2, R = F2[G] = prod of five
components R_j = F_j[Z2^2] indexed by the Frobenius orbits of 3-part character
pairs (xi, eta) = (psi(t_x), psi(t_y)):
    j=0: (1,1) over F2;  j=1: (1,w);  j=2: (w,1);  j=3: (w,w);  j=4: (w,w^2).
With u = 1+s_x, v = 1+s_y:  A_j = (1+eta+eta^2) + u + eta v,
                            B_j = (1+xi+xi^2) + v + xi u,
so A_j is a unit iff eta = 1 (j in {0,2}), B_j a unit iff xi = 1 (j in {0,1}).

Bound: write any element f of F2[G] in s-layers f_s in F2[Z3^2] (s in Z2^2,
|f| = sum_s |f_s|); the 3-part Fourier support of the layer f_s is
    W_s(f) = {j : the [s]-coefficient of f^(psi_j) is nonzero},
and |f_s| >= d3(W_s), where d3(W) = min weight of a nonzero F2[Z3^2]-function
with Fourier support inside W. For b = (Bz, Az) the component data is
V_j^A = A_j z_j, V_j^B = B_j z_j, so

    |b| >= COST(pattern(z)) := sum_s d3({j : s in supp V_j^A})
                             + sum_s d3({j : s in supp V_j^B}).

This script:
  D1  computes d3 by brute force over all 512 functions on Z3^2 and checks it
      depends only on (#nontrivial orbits in W, whether 0 in W) -- the
      GL2(Z3)-symmetry -- and matches the hand dictionary
      (0,T)=9 (1,F)=6 (1,T)=3 (2,F)=4 (2,T)=3 (3,*)=2 (4,F)=2 (4,T)=1;
  D2  enumerates each component's realizable support pairs
      P_j = {(supp V_j^A, supp V_j^B)} by brute force over z_j (256 elements,
      16 for j=0), cross-checking the kernel dims (1,1,1,4,16 elements =
      F2-dims 0,0,0,2,4) and the co-point-or-full structure of radical ideals;
  D3  faithfulness: for actual z in F2[Z6^2] (hexagons, D-pairs, random),
      verifies the partial-Fourier multiplicativity hat(Az)_j = A_j z_j,
      pattern membership in the grammar, COST <= |b|, and tightness
      COST = 6 / 10 on hexagons / D-pairs;
  D4  optimizes COST over the full grammar by a mixed-radix DP on per-layer
      alive-component counts:
        - global min (expect 6, the hexagon pattern);
        - min when any one nontrivial component is dead (per j);
        - the full list of final count-patterns with COST <= 11 in the
          all-components-alive scenario.

Discovery/validation only; never load-bearing in a final analytic proof.
"""
from __future__ import annotations

from itertools import product

import numpy as np

from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.checks import bb_check_matrices

# ----------------------------------------------------------------- F4 arith
# elements 0..3 as bit pairs (lo = 1-part, hi = w-part); w^2 = w + 1
F4_MUL = np.zeros((4, 4), dtype=np.uint8)
for a in range(4):
    for b in range(4):
        a0, a1 = a & 1, a >> 1
        b0, b1 = b & 1, b >> 1
        # (a0 + a1 w)(b0 + b1 w) = a0b0 + (a0b1 + a1b0) w + a1b1 (w+1)
        c0 = (a0 & b0) ^ (a1 & b1)
        c1 = (a0 & b1) ^ (a1 & b0) ^ (a1 & b1)
        F4_MUL[a, b] = c0 | (c1 << 1)
W = 2          # w
W2 = 3         # w^2 = w+1
ONE = 1

def f4mul(a, b): return int(F4_MUL[a, b])
def f4pow(a, k):
    r = 1
    for _ in range(k % 3 if a in (2, 3) else k):
        r = f4mul(r, a)
    return r if a not in (0,) else (1 if k == 0 else 0)

# ------------------------------------------------- F4[Z2^2] group algebra
# elements: length-4 tuples over F4, index s = sx + 2*sy
def conv(a, b):
    out = [0, 0, 0, 0]
    for s1 in range(4):
        if a[s1] == 0:
            continue
        for s2 in range(4):
            if b[s2] == 0:
                continue
            out[s1 ^ s2] ^= f4mul(a[s1], b[s2])
    return tuple(out)

def mask_of(e):
    return sum(1 << s for s in range(4) if e[s] != 0)

# components Ahat_j, Bhat_j are derived EMPIRICALLY below (D0) as the partial
# Fourier transforms of the lab-built d2(delta_0) columns -- this guarantees
# multiplicativity hat(Az)_j = Ahat_j * zhat_j regardless of the circulant
# orientation convention. The hand formulas (1+eta+eta^2) + u + eta*v hold up
# to the orientation relabeling eta <-> eta^2; the unit/radical structure is
# orientation-independent.

# ------------------------------------------------------------- D1: d3 table
print("=== D1: the d3 dictionary over F2[Z3^2] ===")
# characters: psi_(c,d)(t1,t2) = w^(c t1 + d t2); orbit reps:
ORBITS = {0: (0, 0), 1: (0, 1), 2: (1, 0), 3: (1, 1), 4: (1, 2)}
WPOW = [1, W, W2]
def fourier_support(fbits):
    """f given as 9-bit int over t=(t1,t2), idx 3*t1+t2 -> set of live orbits."""
    live = set()
    for j, (c, d) in ORBITS.items():
        acc = 0
        for t1 in range(3):
            for t2 in range(3):
                if (fbits >> (3 * t1 + t2)) & 1:
                    acc ^= WPOW[(c * t1 + d * t2) % 3]
        if acc != 0:
            live.add(j)
    return frozenset(live)

best = {}
for fb in range(1, 512):
    sup = fourier_support(fb)
    wt = bin(fb).count("1")
    for Wset in range(32):                       # all supersets W >= sup
        Wfs = frozenset(j for j in range(5) if (Wset >> j) & 1)
        if sup <= Wfs:
            if Wfs not in best or wt < best[Wfs]:
                best[Wfs] = wt
ok_shape = True
table = {}
for Wfs, wt in best.items():
    key = (len(Wfs - {0}), 0 in Wfs)
    if key in table and table[key] != wt:
        ok_shape = False
    table[key] = wt
print(f"  d3 depends only on (#nontrivial, has-trivial): {ok_shape}")
print(f"  table {{(n, has0): d3}}: {dict(sorted(table.items()))}")
HAND = {(0, True): 9, (1, False): 6, (1, True): 3, (2, False): 4, (2, True): 3,
        (3, False): 2, (3, True): 2, (4, False): 2, (4, True): 1}
print(f"  matches hand dictionary: {all(table.get(k) == v for k, v in HAND.items())}")
COST = {k: v for k, v in table.items()}
COST[(0, False)] = 0

# ------------------------------------- D0: empirical component transforms
print("\n=== D0: empirical Ahat_j, Bhat_j from the lab d2 columns ===")
Gb = ZmZn(6, 6)
Ab = Poly.from_string("x^3 + y + y^2", Gb)
Bb = Poly.from_string("y^3 + x + x^2", Gb)
cm = bb_check_matrices(Ab, Bb)
HZb = cm.H_Z & 1
d2b = HZb.T                                  # z (36) -> qubits (72): (Bz, Az)
nb = 36

def s_of(a, b): return (a % 2) | ((b % 2) << 1)

def field_hat(fvec, block_offset):
    """partial Fourier of one 36-long block (function on Z6^2)."""
    out = {}
    for j, (c, d) in ORBITS.items():
        e = [0, 0, 0, 0]
        for g in Gb:
            if fvec[block_offset + Gb.index(g)]:
                a, b = g
                e[s_of(a, b)] ^= WPOW[(c * (a % 3) + d * (b % 3)) % 3]
        out[j] = tuple(e)
    return out

def zhat(zvec):
    return field_hat(np.concatenate([zvec, np.zeros(nb, np.uint8)]), 0)

col0 = (d2b @ np.eye(nb, dtype=np.uint8)[Gb.index((0, 0))]) % 2
BH = field_hat(col0, 0)                      # block 0 of b = Bz
AH = field_hat(col0, nb)                     # block 1 of b = Az
def aug(e):
    a = 0
    for c in e:
        a ^= c
    return a
for j in range(5):
    print(f"  comp {j}: Ahat = {AH[j]} (aug {aug(AH[j])}), "
          f"Bhat = {BH[j]} (aug {aug(BH[j])})")
print("  expected structure: A unit iff j in {0, x-trivial comp}; "
      "B unit iff j in {0, y-trivial comp}; both radical on two components")

# --------------------------------------------------- D2: component grammars
print("\n=== D2: realizable support-pair grammars per component ===")
ALL_F4 = list(product(range(4), repeat=4))
ALL_F2 = [e for e in ALL_F4 if all(c in (0, 1) for c in e)]
PAIRS = {}
KER_COUNT = {}
for j in range(5):
    dom = ALL_F2 if j == 0 else ALL_F4
    Aj, Bj = AH[j], BH[j]
    pairs = set()
    ker = 0
    for z in dom:
        va, vb = conv(Aj, z), conv(Bj, z)
        if mask_of(va) == 0 and mask_of(vb) == 0:
            ker += 1
        pairs.add((mask_of(va), mask_of(vb)))
    PAIRS[j] = sorted(pairs)
    KER_COUNT[j] = ker
    sizesA = sorted({bin(a).count('1') for a, b in pairs})
    sizesB = sorted({bin(b).count('1') for a, b in pairs})
    print(f"  comp {j}: |pairs| = {len(pairs)}, kernel elements = {ker}, "
          f"|S^A| in {sizesA}, |S^B| in {sizesB}")
print(f"  kernel dims (log2): {[int(np.log2(KER_COUNT[j])) if KER_COUNT[j] else 0 for j in range(5)]} "
      f"(claim: dims 0,0,0,2,4 in some component order)")

# ------------------------------------------------------- D3: faithfulness
print("\n=== D3: faithfulness against real z in F2[Z6^2] ===")

def pattern_cost(zvec):
    zh = zhat(zvec)
    SA = {j: mask_of(conv(AH[j], zh[j])) for j in range(5)}
    SB = {j: mask_of(conv(BH[j], zh[j])) for j in range(5)}
    cost = 0
    for s in range(4):
        nA = sum(1 for j in (1, 2, 3, 4) if (SA[j] >> s) & 1)
        nB = sum(1 for j in (1, 2, 3, 4) if (SB[j] >> s) & 1)
        cost += COST[(nA, bool((SA[0] >> s) & 1))] + COST[(nB, bool((SB[0] >> s) & 1))]
    return cost, SA, SB

rng = np.random.default_rng(20260612)
ok_mult = ok_grammar = ok_bound = True
for trial in range(200):
    zv = rng.integers(0, 2, nb, dtype=np.uint8)
    bvec = (d2b @ zv) % 2
    zh = zhat(zv)
    bh_A = field_hat(bvec, nb)               # A-block = second 36 (b = (Bz, Az))
    bh_B = field_hat(bvec, 0)
    for j in range(5):
        ok_mult &= (bh_A[j] == conv(AH[j], zh[j]))
        ok_mult &= (bh_B[j] == conv(BH[j], zh[j]))
        ok_grammar &= ((mask_of(conv(AH[j], zh[j])), mask_of(conv(BH[j], zh[j]))) in set(PAIRS[j]))
    c, *_ = pattern_cost(zv)
    ok_bound &= (c <= int(bvec.sum()))
print(f"  hat(Az)_j == A_j zhat_j and hat(Bz)_j == B_j zhat_j (200 random z): {ok_mult}")
print(f"  realized pairs always in grammar: {ok_grammar}")
print(f"  COST(pattern) <= |b| always: {ok_bound}")

zhex = np.zeros(nb, np.uint8); zhex[Gb.index((0, 0))] = 1
chex, *_ = pattern_cost(zhex)
print(f"  hexagon: |b| = {int(((d2b @ zhex) % 2).sum())}, COST = {chex} (expect 6 = 6, tight)")
# D-pair: delta in dA, e.g. (0,1)
zpair = np.zeros(nb, np.uint8); zpair[Gb.index((0, 0))] = 1; zpair[Gb.index((0, 1))] = 1
cpair, SA_p, SB_p = pattern_cost(zpair)
print(f"  D-pair (0,1): |b| = {int(((d2b @ zpair) % 2).sum())}, COST = {cpair} (expect 10 = 10, tight)")

# ----------------------------------------------------------- D4: optimizer
print("\n=== D4: optimize COST over the grammar (mixed-radix DP) ===")
# state: counts per layer for A (base-5 digits 0..3) and B (digits 4..7)
POW5 = [5 ** i for i in range(8)]
NSTATE = 5 ** 8

def offsets_of(pairs):
    offs = set()
    for mA, mB in pairs:
        off = 0
        for s in range(4):
            if (mA >> s) & 1:
                off += POW5[s]
            if (mB >> s) & 1:
                off += POW5[4 + s]
        offs.add(off)
    return sorted(offs)

def reach_after(pair_sets):
    reach = np.zeros(NSTATE, dtype=bool)
    reach[0] = True
    for pairs in pair_sets:
        idx = np.flatnonzero(reach)
        new = np.zeros(NSTATE, dtype=bool)
        for off in offsets_of(pairs):
            new[idx + off] = True
        reach = new
    return reach

def best_cost(reach, require_nonzero=True, collect_max=11):
    """min over reachable states and S0 of total cost; also collect <= collect_max."""
    idx = np.flatnonzero(reach)
    digits = np.empty((len(idx), 8), dtype=np.int8)
    rem = idx.copy()
    for pos in range(8):
        digits[:, pos] = rem % 5
        rem //= 5
    best = 10 ** 9
    found = []
    for S0 in range(16):
        f0 = [(S0 >> s) & 1 for s in range(4)]
        costA = np.zeros(len(idx), dtype=np.int64)
        costB = np.zeros(len(idx), dtype=np.int64)
        for s in range(4):
            cA = np.array([COST[(n, bool(f0[s]))] for n in range(5)])
            costA += cA[digits[:, s]]
            costB += cA[digits[:, 4 + s]]
        tot = costA + costB
        if require_nonzero and S0 == 0:
            dead = (idx == 0)
            tot = tot + np.where(dead, 10 ** 9, 0)
        m = int(tot.min())
        best = min(best, m)
        sel = np.flatnonzero(tot <= collect_max)
        for k in sel:
            found.append((int(tot[k]), S0, tuple(int(d) for d in digits[k])))
    return best, found

# Q1: global
reach_all = reach_after([PAIRS[j] for j in (1, 2, 3, 4)])
g_min, _ = best_cost(reach_all)
print(f"  Q1 global min COST (b != 0): {g_min}  (hexagon pattern = 6)")

# Q2: min with one nontrivial component dead
for jdead in (1, 2, 3, 4):
    sets = [(PAIRS[j] if j != jdead else [(0, 0)]) for j in (1, 2, 3, 4)]
    m, _ = best_cost(reach_after(sets))
    print(f"  Q2 min COST with component {jdead} dead: {m}")

# Q3: all four nontrivial components alive: collect <= 11 patterns
alive_sets = [[p for p in PAIRS[j] if p != (0, 0)] for j in (1, 2, 3, 4)]
reach_alive = reach_after(alive_sets)
m_alive, found = best_cost(reach_alive, collect_max=11)
print(f"  Q3 min COST, all nontrivial components alive: {m_alive}")
# canonicalize the <= 11 list modulo the S3-symmetry on layers? just dedupe raw
canon = {}
for tot, S0, dig in found:
    canon.setdefault(tot, set()).add((S0, dig))
print(f"  Q3 patterns with COST <= 11 (count by cost): "
      f"{{c: len(v) for c, v in sorted(canon.items())}}".replace("'", ""))
for c in sorted(canon):
    print(f"    cost {c}: {len(canon[c])} (S0, layer-count) patterns")
    for S0, dig in sorted(canon[c])[:6]:
        print(f"      S0 mask {S0:04b}, A-counts {dig[:4]}, B-counts {dig[4:]}")
    if len(canon[c]) > 6:
        print(f"      ... and {len(canon[c]) - 6} more")

print("\nDone.")
