"""A3 / Track 1.1 Entry 20 — the value-refined offset floor for (M-im).

Entry 19's support-only floor stalled at 6-8: the d3 dictionary sees
component SUPPORTS but the Smith-coset offsets constrain component VALUES
(the wt-24b coset admits the full hexagon support pattern even though no
hexagon lies in it).  This script refines exactly where Entry 19 located
the loss: components {0, 3, 4} become VALUE-exact, components {1, 2} keep
the support grammar.

Why {0, 3, 4}: comp 0 carries the layer parities (and its coset data is
16 diagonal pairs — the parity lemma survives, Entry 19); comps 3, 4 are
the doubly-radical pair where ker d2 lives and where every orbit is
pinned — their joint coset data is tiny and explicit:

    (off_0 + Gamma_0) x (off_3 + Gamma_3) x (off_4 + Gamma_4)
      = 16 x 64 x 16 = 16384 affine value-combos per orbit,

with Gamma_j = {(Bhat_j t, Ahat_j t)} the graph ideal.  Comps 1, 2 are
offset-free (Entry 19: pins are inside {3,4}, so those grammars re-center
to the homogeneous 53 x 53).  The CRT keeps all five coordinates
independent, so the product of the five per-component data sets is the
EXACT image of the coset — the only relaxation left is per-slot:

    |w_{block,s}| >= d3v(v0; a1, a2; v3, v4)
      := min { wt f : f in F2[Z3^2], fhat(psi_0) = v0, fhat(psi_3) = v3,
               fhat(psi_4) = v4, fhat(psi_j) != 0 iff a_j (j = 1, 2) },

an exact 512-entry table (the value 5-tuple <-> layer bijection).
Summing the 8 slots and minimizing over the exact product grammar gives

    min |C(zeta)| >= VFLOOR(zeta).

Sections:
  S1  the value-tuple <-> layer bijection (512 = 2 * 4^4, each tuple hit
      exactly once); the d3v table.
  S2  marginal consistency: d3v marginalized over values reproduces the
      Entry-8 d3 support dictionary on every support set W.
  S3  homogeneous sanity: the zero-offset value-floor equals 6 (the true
      homogeneous minimum — hexagons realize it), achiever census.
  S4  bound validity per orbit rep: random coset elements w satisfy
      OFFCOST(w) <= VCOST(w) <= |w| (refinement sandwich), and
      VFLOOR <= VCOST(canonical rep) <= |canonical rep|.
  S5  VFLOOR(zeta) for all 63 nonzero zeta, by orbit; cross-check <= 12
      (SAT class minima are exactly 12); the verdict "all >= 12?".
  S6  the residual sub-12 landscape per orbit rep (achievers with cost
      <= 11, decoded: comp-0 value, gamma_3, gamma_4, masks at 1, 2) —
      the equality-analysis target list if the verdict fails.

Discovery/validation only; never load-bearing in a final analytic proof.
"""
from __future__ import annotations

from itertools import product

import numpy as np

from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.checks import bb_check_matrices
from bb_lab.linalg import nullspace_f2

# --------------------------------------------------------------- base setup
Gb = ZmZn(6, 6)
Ab = Poly.from_string("x^3 + y + y^2", Gb)
Bb = Poly.from_string("y^3 + x + x^2", Gb)
cmb = bb_check_matrices(Ab, Bb)
HX = (cmb.H_X & 1)
d2b = (cmb.H_Z & 1).T
nb = 36

A_steps = [(3, 0), (0, 1), (0, 2)]
B_steps = [(0, 3), (1, 0), (2, 0)]


def d2c_mat(j):
    d2c = np.zeros((72, nb), np.uint8)
    for g in Gb:
        col = Gb.index(g)
        for blk, steps in ((0, B_steps), (1, A_steps)):
            for (sx, sy) in steps:
                if ((g[0] - j) % 6) + sx >= 6:
                    cell = blk * nb + Gb.index(((g[0] + sx) % 6, (g[1] + sy) % 6))
                    d2c[cell, col] ^= 1
    return d2c


D2C0 = d2c_mat(0)
ker2 = nullspace_f2(d2b)
assert ker2.shape[0] == 6


def span_elems(rows):
    out = []
    for mask in range(1 << rows.shape[0]):
        v = np.zeros(rows.shape[1], np.uint8)
        for i in range(rows.shape[0]):
            if (mask >> i) & 1:
                v ^= rows[i]
        out.append(v)
    return out


Z2all = [z for z in span_elems(ker2) if z.any()]


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

# ------------------------------------------------------------ F4 + CRT frame
F4_MUL = np.zeros((4, 4), dtype=np.uint8)
for a in range(4):
    for b_ in range(4):
        a0, a1 = a & 1, a >> 1
        b0, b1 = b_ & 1, b_ >> 1
        F4_MUL[a, b_] = ((a0 & b0) ^ (a1 & b1)) | \
            ((((a0 & b1) ^ (a1 & b0) ^ (a1 & b1)) << 1))

ORBITS5 = {0: (0, 0), 1: (0, 1), 2: (1, 0), 3: (1, 1), 4: (1, 2)}
WPOW = [1, 2, 3]


def comp_hat(vec36, j):
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
AH = {j: comp_hat((d2b[nb:, :] @ delta0) % 2, j) for j in range(5)}
BH = {j: comp_hat((d2b[:nb, :] @ delta0) % 2, j) for j in range(5)}
assert AH[0] == BH[0]

ALL_F4 = [tuple(t) for t in product(range(4), repeat=4)]
ALL_F2 = [e for e in ALL_F4 if all(c in (0, 1) for c in e)]


def comp_offsets(w72):
    return {j: (comp_hat(w72[:nb], j), comp_hat(w72[nb:], j)) for j in range(5)}


def coset_pairs(offs, j):
    """The exact component-j data set of the coset: off_j + Gamma_j."""
    offL, offR = offs[j]
    dom = ALL_F2 if j == 0 else ALL_F4
    out = {}
    for t in dom:
        out[(xor4(offL, ring_mul4(BH[j], t)),
             xor4(offR, ring_mul4(AH[j], t)))] = True
    return list(out)


def offset_patterns(offs, j):
    return sorted({(mask_of(vL), mask_of(vR)) for vL, vR in coset_pairs(offs, j)})


ZERO_OFFS = {j: ((0, 0, 0, 0), (0, 0, 0, 0)) for j in range(5)}

# =========================================================================
print("=== S1: the value-tuple <-> layer bijection and the d3v table ===")
WT_OF_VAL = np.full((2, 4, 4, 4, 4), -1, np.int8)
for fb in range(512):
    vals = []
    for j, (c, d) in ORBITS5.items():
        acc = 0
        for t1 in range(3):
            for t2 in range(3):
                if (fb >> (3 * t1 + t2)) & 1:
                    acc ^= WPOW[(c * t1 + d * t2) % 3]
        vals.append(acc)
    v0, v1, v2, v3, v4 = vals
    assert v0 in (0, 1)
    assert WT_OF_VAL[v0, v1, v2, v3, v4] == -1, "value tuple hit twice"
    WT_OF_VAL[v0, v1, v2, v3, v4] = bin(fb).count("1")
bij = bool((WT_OF_VAL >= 0).all())
print(f"  every (v0, v1, v2, v3, v4) in F2 x F4^4 realized exactly once: {bij}")

# d3v packed as D3V[(v0*16 + v3*4 + v4)][(a1 + 2*a2)]
D3V = np.full((32, 4), 99, np.int8)
for v0 in range(2):
    for v3 in range(4):
        for v4 in range(4):
            for a1 in range(2):
                for a2 in range(2):
                    dom1 = (0,) if a1 == 0 else (1, 2, 3)
                    dom2 = (0,) if a2 == 0 else (1, 2, 3)
                    m = min(int(WT_OF_VAL[v0, v1, v2, v3, v4])
                            for v1 in dom1 for v2 in dom2)
                    D3V[v0 * 16 + v3 * 4 + v4, a1 + 2 * a2] = m
print(f"  d3v table built (32 x 4), empty layer cell = "
      f"{int(D3V[0, 0])} (claim 0)")

# =========================================================================
print("\n=== S2: d3v marginalizes to the Entry-8 d3 support dictionary ===")
ok_marg = True
for Wm in range(1, 32):
    W = {j for j in range(5) if (Wm >> j) & 1}
    # support-only minimum over nonzero f with supp(fhat) <= W
    best = 99
    for v0 in ((0, 1) if 0 in W else (0,)):
        for v1 in (range(4) if 1 in W else (0,)):
            for v2 in (range(4) if 2 in W else (0,)):
                for v3 in (range(4) if 3 in W else (0,)):
                    for v4 in (range(4) if 4 in W else (0,)):
                        if v0 == v1 == v2 == v3 == v4 == 0:
                            continue
                        best = min(best, int(WT_OF_VAL[v0, v1, v2, v3, v4]))
    n, e = len(W - {0}), 0 in W
    HAND = {(0, True): 9, (1, False): 6, (1, True): 3, (2, False): 4,
            (2, True): 3, (3, False): 2, (3, True): 2, (4, False): 2,
            (4, True): 1}
    ok_marg &= (best == HAND[(n, e)])
print(f"  min over value-assignments inside W == d3(W) for all 31 nonempty W: "
      f"{ok_marg}")

# =========================================================================
# the floor engine
NE_CHUNK = 4096


def vfloor(offs, collect_max=None, forbid_zero=True):
    """Value-exact at comps 0, 3, 4; support grammar at comps 1, 2."""
    cos0 = coset_pairs(offs, 0)
    cos3 = coset_pairs(offs, 3)
    cos4 = coset_pairs(offs, 4)
    g1 = offset_patterns(offs, 1)
    g2 = offset_patterns(offs, 2)
    n0, n3, n4 = len(cos0), len(cos3), len(cos4)
    # per-(block, slot) packed exact index v0*16 + v3*4 + v4
    V = {(c, b): np.array([[pair[b][s] for s in range(4)] for pair in cos],
                          dtype=np.int32)
         for c, cos in ((0, cos0), (3, cos3), (4, cos4)) for b in (0, 1)}
    I0, I3, I4 = np.meshgrid(np.arange(n0), np.arange(n3), np.arange(n4),
                             indexing="ij")
    I0, I3, I4 = I0.ravel(), I3.ravel(), I4.ravel()
    NE = len(I0)
    idxE = np.empty((NE, 2, 4), np.int32)
    for b in (0, 1):
        for s in range(4):
            idxE[:, b, s] = (V[(0, b)][I0, s] * 16 + V[(3, b)][I3, s] * 4 +
                             V[(4, b)][I4, s])
    # support side: all (p1, p2) pattern pairs, packed a1 + 2 a2
    P = len(g1) * len(g2)
    apack = np.empty((P, 2, 4), np.int8)
    for i1, p1 in enumerate(g1):
        for i2, p2 in enumerate(g2):
            p = i1 * len(g2) + i2
            for b in (0, 1):
                for s in range(4):
                    apack[p, b, s] = ((p1[b] >> s) & 1) + 2 * ((p2[b] >> s) & 1)
    # the zero cell (w = 0), to be excluded when present
    try:
        e_zero = next(e for e in range(NE)
                      if not any(any(pair[b]) for c, cos, pair in
                                 ((0, cos0, cos0[I0[e]]),
                                  (3, cos3, cos3[I3[e]]),
                                  (4, cos4, cos4[I4[e]])) for b in (0, 1)))
    except StopIteration:
        e_zero = None
    try:
        p_zero = next(p for p in range(P)
                      if g1[p // len(g2)] == (0, 0) and g2[p % len(g2)] == (0, 0))
    except StopIteration:
        p_zero = None
    best, arg, found = 10 ** 9, None, []
    counts = np.zeros(13, np.int64)               # counts of cost <= 12
    for lo in range(0, NE, NE_CHUNK):
        hi = min(lo + NE_CHUNK, NE)
        C = np.zeros((hi - lo, P), np.int16)
        for b in (0, 1):
            for s in range(4):
                M = D3V[idxE[lo:hi, b, s], :]
                C += M[:, apack[:, b, s]]
        if forbid_zero and e_zero is not None and p_zero is not None \
                and lo <= e_zero < hi:
            C[e_zero - lo, p_zero] = 10 ** 4
        k = int(C.argmin())
        ke, kp = k // P, k % P
        if int(C[ke, kp]) < best:
            best, arg = int(C[ke, kp]), (lo + ke, kp)
        if collect_max is not None:
            small = C[C <= 12]
            if small.size:
                counts += np.bincount(small, minlength=13)[:13]
            for ke, kp in np.argwhere(C <= collect_max):
                found.append((int(C[ke, kp]), lo + int(ke), int(kp)))
    decode = {
        "cos0": cos0, "cos3": cos3, "cos4": cos4, "g1": g1, "g2": g2,
        "I": (I0, I3, I4), "P2": len(g2), "counts": counts,
    }
    return best, arg, found, decode


def vcost_of(w72):
    """VCOST(w) straight from w's component data (validity check)."""
    c = 0
    V = {j: (comp_hat(w72[:nb], j), comp_hat(w72[nb:], j)) for j in range(5)}
    for b in (0, 1):
        for s in range(4):
            a1 = 1 if V[1][b][s] else 0
            a2 = 1 if V[2][b][s] else 0
            c += int(D3V[V[0][b][s] * 16 + V[3][b][s] * 4 + V[4][b][s],
                         a1 + 2 * a2])
    return c


def offcost_of(w72):
    """Entry-19 support-only OFFCOST (for the refinement sandwich)."""
    HANDT = {(0, True): 9, (1, False): 6, (1, True): 3, (2, False): 4,
             (2, True): 3, (3, False): 2, (3, True): 2, (4, False): 2,
             (4, True): 1, (0, False): 0}
    V = {j: (comp_hat(w72[:nb], j), comp_hat(w72[nb:], j)) for j in range(5)}
    c = 0
    for b in (0, 1):
        for s in range(4):
            n = sum(1 for j in (1, 2, 3, 4) if V[j][b][s])
            c += HANDT[(n, bool(V[0][b][s]))]
    return c


# =========================================================================
print("\n=== S3: homogeneous sanity — the zero-offset value-floor ===")
fl0, arg0, found0, dec0 = vfloor(ZERO_OFFS, collect_max=6)
print(f"  zero-offset VFLOOR = {fl0} (true homogeneous minimum 6, hexagons)")
print(f"  achievers with cost <= 6: {len(found0)}")
assert fl0 == 6, "homogeneous value-floor must be exactly 6"

# =========================================================================
print("\n=== S4: validity per orbit rep (refinement sandwich) ===")
rng = np.random.default_rng(20260612)
ok_sand = ok_rep = True
for key in ORBKEYS:
    zrep = np.frombuffer(key, np.uint8).copy()
    w0 = (D2C0 @ zrep) % 2
    offs = comp_offsets(w0)
    for _ in range(200):
        t = rng.integers(0, 2, nb, dtype=np.uint8)
        w = (w0 + d2b @ t) % 2
        oc, vc = offcost_of(w), vcost_of(w)
        ok_sand &= (oc <= vc <= int(w.sum()))
    ok_rep &= (vcost_of(w0) <= int(w0.sum()))
print(f"  OFFCOST(w) <= VCOST(w) <= |w| on 200 random coset elements x 5 "
      f"orbits: {ok_sand}")
print(f"  VCOST(canonical rep) <= |canonical rep| on all 5 orbits: {ok_rep}")

# =========================================================================
print("\n=== S5: the value-refined floors ===")
floors = {}
done = 0
for z in Z2all:
    w0 = (D2C0 @ z) % 2
    offs = comp_offsets(w0)
    fl, _, _, _ = vfloor(offs)
    floors[z.tobytes()] = fl
    done += 1
    if done % 9 == 0:
        print(f"    ... {done}/63 floors computed")
all12 = True
print("\n  floors by orbit:")
for key in ORBKEYS:
    zrep = np.frombuffer(key, np.uint8).copy()
    fls = sorted(floors[z.tobytes()] for z in orbs[key])
    vals = sorted(set(fls))
    all12 &= (fls[0] >= 12)
    print(f"    orbit (n={len(orbs[key])}, wt={int(zrep.sum())}): "
          f"VFLOOR values {vals}")
ok_le12 = all(f <= 12 for f in floors.values())
print(f"\n  cross-check VFLOOR <= 12 everywhere (SAT class minima = 12): "
      f"{ok_le12}")
print(f"  VERDICT — all 63 value-floors >= 12 (closes (M-im) at machine "
      f"level): {all12}")

# =========================================================================
print("\n=== S6/S7: completion sweep — exact kill of the sub-12 combos ===")
# Coset weights are even: |d2c_0 zeta| is even and |d2 t| is even, so any
# coset element of weight <= 11 has weight <= 10, and realizes a combo of
# (even) cost <= 10.  For each such combo, components 0, 3, 4 are
# value-pinned and components 1, 2 are affine graphs: V1R = c1 + rho1 V1L
# (rho1 = Ahat_1 Bhat_1^{-1} radical), V2L = c2 + rho2 V2R.  Enumerating
# V1L inside mask1_L (<= 3^4) and V2R inside mask2_R (<= 3^4), filtering
# on the partner masks, DETERMINES every candidate w exactly (the value
# bijection of S1).  If every completion of every sub-12 combo has weight
# >= 12, then min |C(zeta)| >= 12 — (M-im) for this orbit.

VAL2F = np.full((2, 4, 4, 4, 4), -1, np.int16)
for fb in range(512):
    vals = []
    for j, (c, d) in ORBITS5.items():
        acc = 0
        for t1 in range(3):
            for t2 in range(3):
                if (fb >> (3 * t1 + t2)) & 1:
                    acc ^= WPOW[(c * t1 + d * t2) % 3]
        vals.append(acc)
    VAL2F[vals[0], vals[1], vals[2], vals[3], vals[4]] = fb

# upgrade of the Entry-19 translation transport: ALL 36 translations on a
# basis (with linearity this covers every zeta, so per-orbit kills extend
# to all 63 classes)
K = nullspace_f2(d2b.T)
assert K.shape[0] == 42 and not ((K @ d2b) % 2).any()


def translate72(w, dx, dy):
    out = np.zeros_like(w)
    for blk in (0, 1):
        for g in Gb:
            out[blk * nb + Gb.index(((g[0] + dx) % 6, (g[1] + dy) % 6))] = \
                w[blk * nb + Gb.index(g)]
    return out


ok_tr_full = True
for dx in range(6):
    for dy in range(6):
        for z in ker2:
            dvec = ((D2C0 @ translate36(z, dx, dy)) +
                    translate72((D2C0 @ z) % 2, dx, dy)) % 2
            ok_tr_full &= not ((K @ dvec) % 2).any()
print(f"  class(T zeta) = T class(zeta) for ALL 36 translations x basis: "
      f"{ok_tr_full}")


def inv4(u):
    return next(t for t in ALL_F4 if ring_mul4(u, t) == (1, 0, 0, 0))


def reconstruct_w(v0p, v1L, v1R, v2L, v2R, g3p, g4p):
    """Rebuild w in F2^72 from its full component values (S1 bijection)."""
    w = np.zeros(72, np.uint8)
    for b, (V0, V1, V2, V3, V4) in enumerate(
            ((v0p[0], v1L, v2L, g3p[0], g4p[0]),
             (v0p[1], v1R, v2R, g3p[1], g4p[1]))):
        for s in range(4):
            fb = int(VAL2F[V0[s], V1[s], V2[s], V3[s], V4[s]])
            assert fb >= 0
            for t1 in range(3):
                for t2 in range(3):
                    if (fb >> (3 * t1 + t2)) & 1:
                        # cell with (x%2, y%2) parities of s, (x%3,y%3)=(t1,t2)
                        x = next(v for v in range(6)
                                 if v % 2 == (s & 1) and v % 3 == t1)
                        y = next(v for v in range(6)
                                 if v % 2 == (s >> 1) and v % 3 == t2)
                        w[b * nb + Gb.index((x, y))] = 1
    return w


NONZ = (1, 2, 3)
verdict_mim = True
for key in ORBKEYS:
    zrep = np.frombuffer(key, np.uint8).copy()
    w0 = (D2C0 @ zrep) % 2
    offs = comp_offsets(w0)
    fl, arg, found, dec = vfloor(offs, collect_max=10)
    cos0, cos3, cos4 = dec["cos0"], dec["cos3"], dec["cos4"]
    g1, g2, P2 = dec["g1"], dec["g2"], dec["P2"]
    I0, I3, I4 = dec["I"]
    cnt = {c: int(n) for c, n in enumerate(dec["counts"]) if n and c <= 10}
    # the affine structure of comps 1, 2 (and its verification)
    rho1 = ring_mul4(AH[1], inv4(BH[1]))
    c1 = xor4(offs[1][1], ring_mul4(rho1, offs[1][0]))
    rho2 = ring_mul4(BH[2], inv4(AH[2]))
    c2 = xor4(offs[2][0], ring_mul4(rho2, offs[2][1]))
    ok_aff1 = set(coset_pairs(offs, 1)) == \
        {(v, xor4(c1, ring_mul4(rho1, v))) for v in ALL_F4}
    ok_aff2 = set(coset_pairs(offs, 2)) == \
        {(xor4(c2, ring_mul4(rho2, v)), v) for v in ALL_F4}
    assert ok_aff1 and ok_aff2, "affine-graph structure of comps 1, 2"
    # sweep
    n_complete = 0
    n_empty = 0
    min_wt = 10 ** 9
    n_below12 = 0
    spot = 0
    for cost, e, p in found:
        v0p = cos0[I0[e]]
        g3p = cos3[I3[e]]
        g4p = cos4[I4[e]]
        m1 = g1[p // P2]
        m2 = g2[p % P2]
        cand1 = []
        for vals in product(*[(NONZ if (m1[0] >> s) & 1 else (0,))
                              for s in range(4)]):
            vR = xor4(c1, ring_mul4(rho1, vals))
            if mask_of(vR) == m1[1]:
                cand1.append((vals, vR))
        cand2 = []
        for vals in product(*[(NONZ if (m2[1] >> s) & 1 else (0,))
                              for s in range(4)]):
            vL = xor4(c2, ring_mul4(rho2, vals))
            if mask_of(vL) == m2[0]:
                cand2.append((vL, vals))
        if not cand1 or not cand2:
            n_empty += 1
            continue
        V1L = np.array([a for a, _ in cand1], np.int8)
        V1R = np.array([b for _, b in cand1], np.int8)
        V2L = np.array([a for a, _ in cand2], np.int8)
        V2R = np.array([b for _, b in cand2], np.int8)
        C = np.zeros((len(cand1), len(cand2)), np.int16)
        for s in range(4):
            TL = WT_OF_VAL[v0p[0][s], :, :, g3p[0][s], g4p[0][s]]
            TR = WT_OF_VAL[v0p[1][s], :, :, g3p[1][s], g4p[1][s]]
            C += TL[V1L[:, None, s], V2L[None, :, s]]
            C += TR[V1R[:, None, s], V2R[None, :, s]]
        n_complete += C.size
        m = int(C.min())
        min_wt = min(min_wt, m)
        n_below12 += int((C <= 11).sum())
        # spot-check the reconstruction: coset membership + weight
        if spot < 20:
            ke, kp = np.unravel_index(int(C.argmin()), C.shape)
            wrec = reconstruct_w(v0p, tuple(int(v) for v in V1L[ke]),
                                 tuple(int(v) for v in V1R[ke]),
                                 tuple(int(v) for v in V2L[kp]),
                                 tuple(int(v) for v in V2R[kp]),
                                 g3p, g4p)
            assert int(wrec.sum()) == int(C[ke, kp])
            assert not ((K @ ((wrec + w0) % 2)) % 2).any(), \
                "completion not in the coset!"
            spot += 1
    ok = (n_below12 == 0)
    verdict_mim &= ok
    print(f"  orbit (n={len(orbs[key])}, wt={int(zrep.sum())}): VFLOOR {fl}; "
          f"combos by cost {cnt}; {len(found)} combos, {n_empty} with no "
          f"completion,\n    {n_complete} completions, min completion weight "
          f"{min_wt if min_wt < 10**9 else 'n/a'}, "
          f"completions of weight <= 11: {n_below12} -> "
          f"{'KILLED (>= 12)' if ok else 'SURVIVORS'}")

print(f"\n  VERDICT — every sub-12 combo of every orbit completes only to "
      f"weight >= 12:\n  (M-im) holds at the verified-finite level: "
      f"{verdict_mim}")

print("\nDone.")
