"""A3 / Track 1.1 Entry 19 — the offset-COST DP: machine floors for (M-im).

(M-im): every base 1-cycle in a nonzero im Delta class has weight >= 12,
equivalently dist(d2c_0 zeta, Stab_Z) >= 12 for each of the 63 nonzero
zeta in ker d2.  The cycles in the class Delta[zeta] form the coset

    C(zeta) = d2c_0 zeta + im d2,

and this script lower-bounds min |C(zeta)| by the Entry-8 layer-dictionary
COST, now with an affine offset.

Frame (Entries 7-8): F2[Z6^2] = R_0 x R_1 x ... x R_4 (CRT over the 3-part
characters; R_0 = F2[Z2^2], R_j = F4[Z2^2] for j in 1..4).  For a coset
element w = d2c_0 zeta + d2 t the component data of the two blocks is

    (V_L, V_R)_j = off_j + (Bhat_j that_j, Ahat_j that_j),
    off_j = (comp_j of (d2c_0 zeta)_L, comp_j of (d2c_0 zeta)_R),

with that_j ranging freely and INDEPENDENTLY over R_j (CRT bijection), so
the per-component support-pattern sets multiply EXACTLY across components.
Slot bound: for each of the 8 slots (2 blocks x 4 s-layers in Z2^2),

    |w_{block,s}| >= d3(n, eps),   n = # nontrivial components alive at
                                   the slot, eps = component-0 alive,

(d3 = the Entry-8 dictionary; the slot's layer has Fourier support exactly
the alive set).  Summing the 8 slots:  |w| >= OFFCOST(w), hence

    min |C(zeta)|  >=  FLOOR(zeta) := min over the offset grammar of
                                      sum_slots d3.

Sections:
  L1  zero-offset reproduction of Entry 8 D4: global min 6, achieved by
      exactly the 4 hexagon patterns; min 12 with any one component
      forced dead (j = 0..4).
  L2  bound validity per orbit rep: random coset elements w satisfy
      |w| >= OFFCOST(w); realized component patterns lie in the offset
      grammar; the affine multiplicativity hat(w)_j = off_j + (Bhat that,
      Ahat that) holds exactly.
  L3  transport checks: d2c_0 zeta is a 1-cycle; the class [d2c_j zeta]
      is cut-independent; translation covariance of classes; the swap
      builder identity Shat(d2c^x_0 zeta) = d2c^y_0(S zeta) and the swap
      class question Delta^y =? Delta^x on H2 (decides whether the
      5 translation+swap orbits transport, or only translation orbits).
  L4  M8 cross-check: the offset grammar misses (0,0) exactly at the
      pinned components; every orbit pinned inside {3,4}.
  M   FLOOR(zeta) for all 63 nonzero zeta, grouped by orbit; cross-check
      FLOOR <= 12 (SAT class minima are exactly 12); the verdict
      "all floors >= 12?"; witness decompositions at the floor per orbit
      rep; sub-12 achievable-pattern census per orbit rep if any floor
      falls short (the equality-analysis target list).

Discovery/validation only; never load-bearing in a final analytic proof.
"""
from __future__ import annotations

from itertools import product

import numpy as np

from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.checks import bb_check_matrices
from bb_lab.linalg import nullspace_f2, rank_f2

# --------------------------------------------------------------- base setup
Gb = ZmZn(6, 6)
Ab = Poly.from_string("x^3 + y + y^2", Gb)
Bb = Poly.from_string("y^3 + x + x^2", Gb)
cmb = bb_check_matrices(Ab, Bb)
HX = (cmb.H_X & 1)                       # d1 = (A | B), 36 x 72
d2b = (cmb.H_Z & 1).T                    # d2 = (B ; A), 72 x 36
nb = 36

A_steps = [(3, 0), (0, 1), (0, 2)]       # A = x^3 + y + y^2
B_steps = [(0, 3), (1, 0), (2, 0)]       # B = y^3 + x + x^2


def d2_mats(j, axis=0):
    """Split d2 = (B; A) into (non-crossing, crossing) parts for cut j
    along the given axis (0 = x-cuts, 1 = y-cuts)."""
    d2nc = np.zeros((72, nb), np.uint8)
    d2c = np.zeros((72, nb), np.uint8)
    for g in Gb:
        col = Gb.index(g)
        for blk, steps in ((0, B_steps), (1, A_steps)):
            for (sx, sy) in steps:
                cell = blk * nb + Gb.index(((g[0] + sx) % 6, (g[1] + sy) % 6))
                tgt = d2c if ((g[axis] - j) % 6) + (sx, sy)[axis] >= 6 else d2nc
                tgt[cell, col] ^= 1
    return d2nc, d2c


D2C = {j: d2_mats(j)[1] for j in range(6)}               # x-cut crossing parts
D2C0Y = d2_mats(0, axis=1)[1]                            # y-cut 0 crossing part
assert all(((d2_mats(j)[0] ^ D2C[j]) == d2b).all() for j in range(6))

ker2 = nullspace_f2(d2b)                                 # ker d2, dim 6
K = nullspace_f2(d2b.T)                                  # 42-bit syndrome key
assert ker2.shape[0] == 6 and K.shape[0] == 42
assert not ((K @ d2b) % 2).any()


def in_stab(w):
    """w in im d2  <=>  K w = 0 (the Entry-9 syndrome-key membership)."""
    return not ((K @ w) % 2).any()


def span_elems(rows):
    out = []
    for mask in range(1 << rows.shape[0]):
        v = np.zeros(rows.shape[1], np.uint8)
        for i in range(rows.shape[0]):
            if (mask >> i) & 1:
                v ^= rows[i]
        out.append(v)
    return out


Z2all = [z for z in span_elems(ker2) if z.any()]         # the 63 nonzero zeta


def translate36(z, dx, dy):
    out = np.zeros_like(z)
    for g in Gb:
        out[Gb.index(((g[0] + dx) % 6, (g[1] + dy) % 6))] = z[Gb.index(g)]
    return out


def swap36(z):
    out = np.zeros_like(z)
    for g in Gb:
        out[Gb.index((g[1], g[0]))] = z[Gb.index(g)]
    return out


def translate72(w, dx, dy):
    out = np.zeros_like(w)
    for blk in (0, 1):
        for g in Gb:
            out[blk * nb + Gb.index(((g[0] + dx) % 6, (g[1] + dy) % 6))] = \
                w[blk * nb + Gb.index(g)]
    return out


def swap72(w):
    """Shat(w_L, w_R) = (S w_R, S w_L) — the x<->y code automorphism."""
    out = np.zeros_like(w)
    for g in Gb:
        out[Gb.index((g[1], g[0]))] = w[nb + Gb.index(g)]
        out[nb + Gb.index((g[1], g[0]))] = w[Gb.index(g)]
    return out


# orbits of ker d2 \ 0 under translation + swap (M1 reproduction)
orbs = {}
for z in Z2all:
    cands = []
    for dx in range(6):
        for dy in range(6):
            t = translate36(z, dx, dy)
            cands.append(t.tobytes())
            cands.append(swap36(t).tobytes())
    orbs.setdefault(min(cands), []).append(z)
ORBKEYS = sorted(orbs, key=lambda k: (int(np.frombuffer(k, np.uint8).sum()),
                                      len(orbs[k])))
print("=== setup: orbits of ker d2 \\ 0 under translation + swap ===")
print(f"  orbits (size, weight): "
      f"{[(len(orbs[k]), int(np.frombuffer(k, np.uint8).sum())) for k in ORBKEYS]}")
# translation-only orbits, for the transport bookkeeping
torbs = {}
for z in Z2all:
    cands = [translate36(z, dx, dy).tobytes()
             for dx in range(6) for dy in range(6)]
    torbs.setdefault(min(cands), []).append(z)
print(f"  translation-only orbits: {len(torbs)} with sizes "
      f"{sorted(len(v) for v in torbs.values())}")

# ------------------------------------------------------------ F4 + CRT frame
F4_MUL = np.zeros((4, 4), dtype=np.uint8)
for a in range(4):
    for b_ in range(4):
        a0, a1 = a & 1, a >> 1
        b0, b1 = b_ & 1, b_ >> 1
        F4_MUL[a, b_] = ((a0 & b0) ^ (a1 & b1)) | \
            ((((a0 & b1) ^ (a1 & b0) ^ (a1 & b1)) << 1))

ORBITS5 = {0: (0, 0), 1: (0, 1), 2: (1, 0), 3: (1, 1), 4: (1, 2)}
WPOW = [1, 2, 3]                                          # 1, w, w^2


def comp_hat(vec36, j):
    """Component-j partial Fourier transform of a function on Z6^2,
    as an element of F4[Z2^2] (length-4 tuple, index s = sx + 2 sy)."""
    out = [0, 0, 0, 0]
    c, d = ORBITS5[j]
    for g in Gb:
        if vec36[Gb.index(g)]:
            s = (g[0] % 2) | ((g[1] % 2) << 1)
            out[s] ^= WPOW[(c * (g[0] % 3) + d * (g[1] % 3)) % 3]
    return tuple(out)


def ring_mul4(f, g):
    out = [0, 0, 0, 0]
    for s1 in range(4):
        if f[s1]:
            for s2 in range(4):
                if g[s2]:
                    out[s1 ^ s2] ^= int(F4_MUL[f[s1], g[s2]])
    return tuple(out)


def xor4(a, b):
    return tuple(x ^ y for x, y in zip(a, b))


def mask_of(e):
    return sum(1 << s for s in range(4) if e[s])


delta0 = np.eye(nb, dtype=np.uint8)[Gb.index((0, 0))]
colB = (d2b[:nb, :] @ delta0) % 2                         # B-block of d2(delta_0)
colA = (d2b[nb:, :] @ delta0) % 2
AH = {j: comp_hat(colA, j) for j in range(5)}
BH = {j: comp_hat(colB, j) for j in range(5)}
assert AH[0] == BH[0], "parity lemma: Ahat_0 = Bhat_0 = [1]+[s_x]+[s_y]"

# ------------------------------------------------------------- the d3 table
print("\n=== d3 dictionary (rebuilt, checked against the Entry-8 hand table) ===")


def fourier_support(fbits):
    live = set()
    for j, (c, d) in ORBITS5.items():
        acc = 0
        for t1 in range(3):
            for t2 in range(3):
                if (fbits >> (3 * t1 + t2)) & 1:
                    acc ^= WPOW[(c * t1 + d * t2) % 3]
        if acc:
            live.add(j)
    return frozenset(live)


best_w = {}
for fb in range(1, 512):
    sup = fourier_support(fb)
    wt = bin(fb).count("1")
    for Wset in range(32):
        Wfs = frozenset(j for j in range(5) if (Wset >> j) & 1)
        if sup <= Wfs and (Wfs not in best_w or wt < best_w[Wfs]):
            best_w[Wfs] = wt
D3 = {}
for Wfs, wt in best_w.items():
    key = (len(Wfs - {0}), 0 in Wfs)
    assert D3.get(key, wt) == wt
    D3[key] = wt
D3[(0, False)] = 0
HAND = {(0, True): 9, (1, False): 6, (1, True): 3, (2, False): 4, (2, True): 3,
        (3, False): 2, (3, True): 2, (4, False): 2, (4, True): 1, (0, False): 0}
print(f"  d3 == hand table: {D3 == HAND}")
D3L = np.array([[D3[(n, False)] for n in range(5)],
                [D3[(n, True)] for n in range(5)]], dtype=np.int64)

# ------------------------------------------------------- the offset grammar
ALL_F4 = [tuple(t) for t in product(range(4), repeat=4)]
ALL_F2 = [e for e in ALL_F4 if all(c in (0, 1) for c in e)]


def comp_offsets(w72):
    return {j: (comp_hat(w72[:nb], j), comp_hat(w72[nb:], j)) for j in range(5)}


def offset_patterns(offs, j):
    """Realizable (mask_L, mask_R) support pairs of component j over the
    coset: off_j + (Bhat_j that, Ahat_j that), that in R_j."""
    offL, offR = offs[j]
    dom = ALL_F2 if j == 0 else ALL_F4
    pats = set()
    for t in dom:
        pats.add((mask_of(xor4(offL, ring_mul4(BH[j], t))),
                  mask_of(xor4(offR, ring_mul4(AH[j], t)))))
    return sorted(pats)


ZERO_OFFS = {j: ((0, 0, 0, 0), (0, 0, 0, 0)) for j in range(5)}

# ------------------------------------------------------------------- the DP
POW5 = [5 ** i for i in range(8)]
NSTATE = 5 ** 8
DIGITS_ALL = np.empty((NSTATE, 8), dtype=np.int8)
_rem = np.arange(NSTATE)
for _pos in range(8):
    DIGITS_ALL[:, _pos] = _rem % 5
    _rem //= 5


def offsets_of(pairs):
    offs = {}
    for mL, mR in pairs:
        off = 0
        for s in range(4):
            if (mL >> s) & 1:
                off += POW5[s]
            if (mR >> s) & 1:
                off += POW5[4 + s]
        offs.setdefault(off, (mL, mR))
    return offs


def reach_after(pattern_sets, parents=False):
    """Boolean reachability over per-slot alive counts; optionally keep one
    witness pattern per state per stage for decoding."""
    reach = np.zeros(NSTATE, dtype=bool)
    reach[0] = True
    pars = []
    for pats in pattern_sets:
        idx = np.flatnonzero(reach)
        new = np.zeros(NSTATE, dtype=bool)
        par = np.full(NSTATE, -1, dtype=np.int32) if parents else None
        offmap = offsets_of(pats)
        for off in offmap:
            tgt = idx + off
            new[tgt] = True
            if parents:
                par[tgt] = off
        reach = new
        pars.append((par, offmap))
    return (reach, pars) if parents else reach


def floor_of(pattern_sets, collect_max=None, forbid_zero=True, decode=False):
    """min over the grammar (comp-0 pattern pairs x reachable count states)
    of sum_slots d3; optionally collect all combos with cost <= collect_max
    and decode one witness decomposition of an argmin."""
    if decode:
        reach, pars = reach_after(pattern_sets[1:], parents=True)
    else:
        reach = reach_after(pattern_sets[1:])
    idx = np.flatnonzero(reach)
    digits = DIGITS_ALL[idx]
    best, arg, found = 10 ** 9, None, []
    for (mL0, mR0) in pattern_sets[0]:
        tot = np.zeros(len(idx), dtype=np.int64)
        for s in range(4):
            tot += D3L[(mL0 >> s) & 1][digits[:, s]]
            tot += D3L[(mR0 >> s) & 1][digits[:, 4 + s]]
        if forbid_zero and mL0 == 0 and mR0 == 0:
            tot = tot + np.where(idx == 0, 10 ** 9, 0)
        k = int(tot.argmin())
        if int(tot[k]) < best:
            best, arg = int(tot[k]), ((mL0, mR0), int(idx[k]))
        if collect_max is not None:
            for kk in np.flatnonzero(tot <= collect_max):
                found.append((int(tot[kk]), (mL0, mR0),
                              tuple(int(d) for d in digits[kk])))
    witness = None
    if decode and arg is not None:
        comp0, state = arg
        comps = []
        for par, offmap in reversed(pars):
            off = int(par[state])
            comps.append(offmap[off])
            state -= off
        witness = (comp0, list(reversed(comps)))
    return best, found, witness


# =========================================================================
print("\n=== L1: zero-offset reproduction of Entry 8 D4 ===")
pats_zero = [offset_patterns(ZERO_OFFS, j) for j in range(5)]
sizes = [len(p) for p in pats_zero]
print(f"  homogeneous grammar sizes per component: {sizes} "
      f"(Entry 8: 16, 53, 53, 20, 6)")
g_min, g_found, _ = floor_of(pats_zero, collect_max=6)
print(f"  global min COST (b != 0): {g_min} (Entry 8: 6)")
print(f"  patterns with COST <= 6: {len(g_found)} (Entry 8: the 4 hexagon "
      f"patterns)")
hex_like = all(
    cost == 6
    and bin(mLR[0]).count("1") == 3 and mLR[0] == mLR[1]
    and all(d in (0, 4) for d in dig)
    and sum(dig[:4]) == 12 == sum(dig[4:])
    and all((dig[s] == 4) == bool((mLR[0] >> s) & 1) for s in range(4))
    and all((dig[4 + s] == 4) == bool((mLR[0] >> s) & 1) for s in range(4))
    for cost, mLR, dig in g_found)
print(f"  all of them hexagon-type (S0 a co-point, both blocks full on its "
      f"3 layers): {hex_like}")
for jdead in range(5):
    sets = list(pats_zero)
    sets[jdead] = [(0, 0)]
    m, _, _ = floor_of(sets)
    print(f"  min COST with component {jdead} forced dead: {m} (Entry 8: 12)")

# =========================================================================
print("\n=== L2: bound validity on random coset elements (per orbit rep) ===")
rng = np.random.default_rng(20260612)


def offcost(w72):
    """OFFCOST(w) straight from w's component transforms (no grammar)."""
    VL = {j: comp_hat(w72[:nb], j) for j in range(5)}
    VR = {j: comp_hat(w72[nb:], j) for j in range(5)}
    c = 0
    for s in range(4):
        nL = sum(1 for j in (1, 2, 3, 4) if VL[j][s])
        nR = sum(1 for j in (1, 2, 3, 4) if VR[j][s])
        c += D3[(nL, bool(VL[0][s]))] + D3[(nR, bool(VR[0][s]))]
    return c


ok_bound = ok_grammar = ok_affine = True
for key in ORBKEYS:
    zrep = np.frombuffer(key, np.uint8).copy()
    w0 = (D2C[0] @ zrep) % 2
    offs = comp_offsets(w0)
    psets = [set(offset_patterns(offs, j)) for j in range(5)]
    for _ in range(200):
        t = rng.integers(0, 2, nb, dtype=np.uint8)
        w = (w0 + d2b @ t) % 2
        that = {j: comp_hat(t, j) for j in range(5)}
        for j in range(5):
            vL, vR = comp_hat(w[:nb], j), comp_hat(w[nb:], j)
            ok_affine &= (vL == xor4(offs[j][0], ring_mul4(BH[j], that[j])))
            ok_affine &= (vR == xor4(offs[j][1], ring_mul4(AH[j], that[j])))
            ok_grammar &= ((mask_of(vL), mask_of(vR)) in psets[j])
        ok_bound &= (offcost(w) <= int(w.sum()))
print(f"  affine multiplicativity hat(w)_j = off_j + (Bhat that, Ahat that): "
      f"{ok_affine}")
print(f"  realized component patterns always in the offset grammar: {ok_grammar}")
print(f"  |w| >= OFFCOST(w) on 200 random coset elements x 5 orbits: {ok_bound}")

# =========================================================================
print("\n=== L3: transport checks ===")
ok_cyc = all(not ((HX @ ((D2C[0] @ z) % 2)) % 2).any() for z in Z2all)
print(f"  d2c_0 zeta is a 1-cycle for all 63 zeta: {ok_cyc}")
ok_cut = all(in_stab(((D2C[j] ^ D2C[0]) @ z) % 2) for j in range(1, 6)
             for z in ker2)
print(f"  [d2c_j zeta] cut-independent (all j, basis zeta): {ok_cut}")
ok_tr = True
for (dx, dy) in [(1, 0), (0, 1), (2, 3), (5, 5)]:
    for z in ker2:
        lhs = (D2C[0] @ translate36(z, dx, dy)) % 2
        rhs = translate72((D2C[0] @ z) % 2, dx, dy)
        ok_tr &= in_stab((lhs + rhs) % 2)
print(f"  class(T zeta) = T class(zeta) (4 sample translations): {ok_tr}")
ok_swb = all((swap72((D2C[0] @ z) % 2) == (D2C0Y @ swap36(z)) % 2).all()
             for z in ker2)
print(f"  builder identity Shat(d2c^x_0 zeta) = d2c^y_0(S zeta): {ok_swb}")
ok_ycyc = all(not ((HX @ ((D2C0Y @ z) % 2)) % 2).any() for z in ker2)
swap_classes_eq = all(in_stab(((D2C0Y ^ D2C[0]) @ z) % 2) for z in ker2)
print(f"  d2c^y_0 zeta is a 1-cycle (basis): {ok_ycyc}")
print(f"  Delta^y == Delta^x on H2 (y-cut and x-cut connecting maps agree): "
      f"{swap_classes_eq}")
# even if the maps differ pointwise, the IMAGES may coincide as subspaces
FX = np.vstack([d2b.T, ((D2C[0] @ ker2.T) % 2).T])       # spans flux-silent cycles
FXY = np.vstack([FX, ((D2C0Y @ ker2.T) % 2).T])
span_eq = rank_f2(FX) == rank_f2(FXY)
print(f"  im Delta^y == im Delta^x as subspaces of H1: {span_eq} "
      f"(rank {rank_f2(FX)} vs {rank_f2(FXY)})")
print("    -> transport note: the translation-only orbits already equal the"
      " 5 swap orbits, so the 5-rep reduction needs only translation"
      " covariance (verified above); the Delta^y question is informational.")

# =========================================================================
print("\n=== L4: pinned components (M8 cross-check) ===")
PIN_OK = True
orb_data = {}
for key in ORBKEYS:
    zrep = np.frombuffer(key, np.uint8).copy()
    w0 = (D2C[0] @ zrep) % 2
    offs = comp_offsets(w0)
    psets = [offset_patterns(offs, j) for j in range(5)]
    pins = {j for j in range(5) if (0, 0) not in psets[j]}
    orb_data[key] = (zrep, offs, psets, pins)
    PIN_OK &= bool(pins) and pins <= {3, 4}
    print(f"  orbit (n={len(orbs[key])}, wt={int(zrep.sum())}): pinned {sorted(pins)}; "
          f"grammar sizes {[len(p) for p in psets]}")
print(f"  every orbit pinned, inside {{3,4}} (M8): {PIN_OK}")
diag0 = all(orb_data[key][1][0][0] == orb_data[key][1][0][1] for key in ORBKEYS)
print(f"  comp-0 offsets diagonal (off_L = off_R), i.e. the coset keeps the "
      f"parity lemma\n  (both blocks share layer parities, as for "
      f"stabilizers): {diag0}")

# =========================================================================
print("\n=== M: the offset-COST floors ===")
print("  per-orbit canonical-rep weights (context; class minima are <= these):")
for key in ORBKEYS:
    zrep = orb_data[key][0]
    dws = [int(((D2C[j] @ zrep) % 2).sum()) for j in range(6)]
    print(f"    orbit (n={len(orbs[key])}, wt={int(zrep.sum())}): "
          f"|d2c_j zeta| = {dws}")

floors = {}
done = 0
for z in Z2all:
    w0 = (D2C[0] @ z) % 2
    offs = comp_offsets(w0)
    psets = [offset_patterns(offs, j) for j in range(5)]
    assert not all((0, 0) in set(p) for p in psets), \
        "0 in the coset of a nonzero zeta (Delta not injective?!)"
    fl, _, _ = floor_of(psets)
    floors[z.tobytes()] = fl
    done += 1
    if done % 9 == 0:
        print(f"    ... {done}/63 floors computed")

print("\n  floors by translation+swap orbit:")
all12 = True
for key in ORBKEYS:
    zrep = orb_data[key][0]
    fls = sorted(floors[z.tobytes()] for z in orbs[key])
    vals = sorted(set(fls))
    all12 &= (fls[0] >= 12)
    print(f"    orbit (n={len(orbs[key])}, wt={int(zrep.sum())}): "
          f"floor values {vals} (multiset min {fls[0]}, max {fls[-1]})")
ok_le12 = all(f <= 12 for f in floors.values())
print(f"\n  cross-check FLOOR <= 12 everywhere (SAT: class minima = 12): {ok_le12}")
print(f"  VERDICT — all 63 floors >= 12 (closes (M-im) at machine level): {all12}")

print("\n  witness decompositions at the floor (orbit reps):")
for key in ORBKEYS:
    zrep, offs, psets, pins = orb_data[key]
    fl, _, wit = floor_of(psets, decode=True)
    comp0, comps = wit
    desc = [f"j0:(L={comp0[0]:04b},R={comp0[1]:04b})"] + \
           [f"j{j}:(L={mL:04b},R={mR:04b})" for j, (mL, mR) in
            enumerate(comps, start=1)]
    print(f"    orbit (n={len(orbs[key])}, wt={int(zrep.sum())}): floor {fl}; "
          f"alive masks {' '.join(desc)}")

if not all12:
    print("\n  sub-12 achievable-pattern census per orbit rep (equality-analysis "
          "targets):")
    for key in ORBKEYS:
        zrep, offs, psets, pins = orb_data[key]
        fl, found, _ = floor_of(psets, collect_max=11)
        if fl >= 12:
            print(f"    orbit (n={len(orbs[key])}, wt={int(zrep.sum())}): "
                  f"floor {fl} — no sub-12 patterns")
            continue
        bycost = {}
        for cost, mLR, dig in found:
            bycost.setdefault(cost, []).append((mLR, dig))
        cnt = {c: len(v) for c, v in sorted(bycost.items())}
        print(f"    orbit (n={len(orbs[key])}, wt={int(zrep.sum())}): "
              f"floor {fl}; sub-12 pattern counts by cost: {cnt}")
        for c in sorted(bycost)[:1]:
            for mLR, dig in bycost[c][:4]:
                print(f"      cost {c}: comp0 (L={mLR[0]:04b},R={mLR[1]:04b}), "
                      f"L-counts {dig[:4]}, R-counts {dig[4:]}")

print("\nDone.")
