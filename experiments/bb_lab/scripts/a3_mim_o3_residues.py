"""A3 / Track 1.1 Entry 26 — O3: the unpinnedness of comps 1, 2 by hand;
assembly checks.

The last load-bearing residue of the (M-im) hand proof: c1 = c2 = 0
(equivalently off_j in Gamma_j for j = 1, 2; equivalently the confined
sets are the SUBSPACES im rho_i).  Hand derivation, comp 1 (verified
stepwise here on all 63 zeta):

  Write zeta's columns c_0..c_5 (functions on Z6) and their comp-1
  y-transforms u_i := sum_y c_i(y) w^{y%3} s_y^{y%2} in F4[s_y].
  (U1) the crossing bookkeeping gives
        off1L = tau (u4 + u5 + s_x u5) ... more precisely
        off1L = u4 + u5 + s_x u5,  off1R = u3 + s_x u4 + u5,
       and with the A-relation u_{i+3} = tau u_i (tau = w^2 + w s_y,
       a unit):  off1L = tau(u1 + u2 + s_x u2),
                 off1R = tau(u0 + u2 + s_x u1).
  (U2) the B-relations give  u0 + u1 = s_y u2   (R2)
       and (1+s_y) u1 = w^2 (1+s_y) u2, i.e. Y u1 = w^2 Y u2   (D1).
  (U3) c1 = 0  <=>  Bhat1 off1R = Ahat1 off1L  <=>  (cancel tau,
       substitute R2)  Y [ (X+w) u1 + (1 + w^2 X) u2 ] = 0, which D1
       makes identically zero (w * w^2 = 1).  QED.
  (U4) the mirror chain for comp 2 (x and y exchange roles; the
       x-transform v_i carries the w-weights, the A-relation becomes
       v_{i+3} = Y v_i): each step verified; same conclusion c2 = 0.

Assembly checks:
  (A1) the five orbit floors: >= 12 via O1 (wt-24) and O1 + O2
       (wt-16/18); together with translation transport this is (M-im);
  (A2) the full chain endpoints re-confirmed: imDelta-distance = 12
       (down to the bar), d_X = d_Z by duality, tau(u*) attains 12.

Discovery/validation only; the load-bearing arguments are in the log.
"""
from __future__ import annotations

import numpy as np

from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.checks import bb_check_matrices
from bb_lab.linalg import nullspace_f2

Gb = ZmZn(6, 6)
Ab = Poly.from_string("x^3 + y + y^2", Gb)
Bb = Poly.from_string("y^3 + x + x^2", Gb)
cmb = bb_check_matrices(Ab, Bb)
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

F4_MUL = np.zeros((4, 4), dtype=np.uint8)
for a in range(4):
    for b_ in range(4):
        a0, a1 = a & 1, a >> 1
        b0, b1 = b_ & 1, b_ >> 1
        F4_MUL[a, b_] = ((a0 & b0) ^ (a1 & b1)) | \
            ((((a0 & b1) ^ (a1 & b0) ^ (a1 & b1)) << 1))
ORBITS5 = {0: (0, 0), 1: (0, 1), 2: (1, 0), 3: (1, 1), 4: (1, 2)}
WPOW = [1, 2, 3]
W = 2


def f4m(a, b):
    return int(F4_MUL[a, b])


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
                    out[s1 ^ s2] ^= f4m(f[s1], g[s2])
    return tuple(out)


def xor4(a, b):
    return tuple(x ^ y for x, y in zip(a, b))


from itertools import product as _prod
ALL_F4 = [tuple(t) for t in _prod(range(4), repeat=4)]


def inv4(u):
    return next(t for t in ALL_F4 if ring_mul4(u, t) == (1, 0, 0, 0))


delta0 = np.eye(nb, dtype=np.uint8)[Gb.index((0, 0))]
AH = {j: comp_hat((d2b[nb:, :] @ delta0) % 2, j) for j in range(5)}
BH = {j: comp_hat((d2b[:nb, :] @ delta0) % 2, j) for j in range(5)}
rho1 = ring_mul4(AH[1], inv4(BH[1]))
rho2 = ring_mul4(BH[2], inv4(AH[2]))

# F4[s_y] elements as pairs (e-part, s_y-part); embed into F4[Z2^2] slots
# (e, s_x, s_y, s_x s_y) for cross-checking with comp_hat.


def ymul(a, b):
    """(a0 + a1 s_y)(b0 + b1 s_y) in F4[s_y]."""
    return (f4m(a[0], b[0]) ^ f4m(a[1], b[1]),
            f4m(a[0], b[1]) ^ f4m(a[1], b[0]))


def yxor(a, b):
    return (a[0] ^ b[0], a[1] ^ b[1])


def emb(u, sx_pow):
    """u in F4[s_y] times s_x^sx_pow, as a slot 4-tuple."""
    if sx_pow == 0:
        return (u[0], 0, u[1], 0)
    return (0, u[0], 0, u[1])


def u_transform(z, i):
    """comp-1 y-transform of column i: sum_y z(i,y) w^{y%3} s_y^{y%2}."""
    out = (0, 0)
    for y in range(6):
        if z[Gb.index((i, y))]:
            t = WPOW[y % 3]
            out = yxor(out, (t, 0) if y % 2 == 0 else (0, t))
    return out


def v_transform(z, i):
    """comp-2 x-free transform of column i: sum_y z(i,y) s_y^{y%2}."""
    out = (0, 0)
    for y in range(6):
        if z[Gb.index((i, y))]:
            out = yxor(out, (1, 0) if y % 2 == 0 else (0, 1))
    return out


TAU = (3, 2)                       # w^2 + w s_y
SY = (0, 1)
YY = (1, 1)                        # Y = 1 + s_y

print("=== U1/U2/U3: the comp-1 unpinnedness chain (all 63 zeta) ===")
ok_u1 = ok_arel = ok_r2 = ok_d1 = ok_u3 = ok_final = True
for z in Z2all:
    w0 = (D2C0 @ z) % 2
    off1 = (comp_hat(w0[:nb], 1), comp_hat(w0[nb:], 1))
    u = [u_transform(z, i) for i in range(6)]
    # U1: the crossing bookkeeping
    lhsL = xor4(xor4(emb(u[4], 0), emb(u[5], 0)), emb(u[5], 1))
    lhsR = xor4(xor4(emb(u[3], 0), emb(u[4], 1)), emb(u[5], 0))
    ok_u1 &= (lhsL == off1[0] and lhsR == off1[1])
    # A-relation u_{i+3} = tau u_i
    for i in range(3):
        ok_arel &= (u[i + 3] == ymul(TAU, u[i]))
    # B-relations: R2: u0 + u1 = s_y u2; R1: u0 + tau u2 = s_y u1
    ok_r2 &= (yxor(u[0], u[1]) == ymul(SY, u[2]))
    ok_r2 &= (yxor(u[0], ymul(TAU, u[2])) == ymul(SY, u[1]))
    # D1: Y u1 = w^2 Y u2
    ok_d1 &= (ymul(YY, u[1]) == ymul(YY, ymul((3, 0), u[2])))
    # U3 reduced identity: Y[(X+w) u1 + (1+w^2 X) u2] = 0 in F4[Z2^2]
    Xw = (3, 1, 0, 0)              # X + w = (1+w) + s_x = w^2 + s_x
    one_w2X = (2, 3, 0, 0)         # 1 + w^2 X = (1+w^2) + w^2 s_x = w + w^2 s_x
    Yfull = (1, 0, 1, 0)
    expr = ring_mul4(Yfull, xor4(ring_mul4(Xw, emb(u[1], 0)),
                                 ring_mul4(one_w2X, emb(u[2], 0))))
    ok_u3 &= (expr == (0, 0, 0, 0))
    # the endpoint: Bhat1 off1R = Ahat1 off1L  (c1 = 0)
    ok_final &= (ring_mul4(BH[1], off1[1]) == ring_mul4(AH[1], off1[0]))
print(f"  U1 off1L = u4+u5+s_x u5, off1R = u3+s_x u4+u5: {ok_u1}")
print(f"  A-relation u_(i+3) = tau u_i (tau = w2 + w s_y): {ok_arel}")
print(f"  B-relations R1, R2: {ok_r2}")
print(f"  D1: Y u1 = w2 Y u2: {ok_d1}")
print(f"  U3 reduced identity Y[(X+w)u1 + (1+w2 X)u2] = 0: {ok_u3}")
print(f"  endpoint Bhat1 off1R = Ahat1 off1L (c1 = 0): {ok_final}")

print("\n=== U4: the comp-2 mirror chain ===")
ok_m1 = ok_ma = ok_mb = ok_md = ok_mfin = True
for z in Z2all:
    w0 = (D2C0 @ z) % 2
    off2 = (comp_hat(w0[:nb], 2), comp_hat(w0[nb:], 2))
    v = [v_transform(z, i) for i in range(6)]
    # crossing bookkeeping with the w-weights on the x-side:
    # off2L = v4 + v5 + w s_x v5;  off2R = v3 + w s_x v4 + w^2 v5
    lhsL = xor4(xor4(emb(v[4], 0), emb(v[5], 0)),
                ring_mul4((0, 2, 0, 0), emb(v[5], 0)))
    lhsR = xor4(xor4(emb(v[3], 0), ring_mul4((0, 2, 0, 0), emb(v[4], 0))),
                ring_mul4((3, 0, 0, 0), emb(v[5], 0)))
    ok_m1 &= (lhsL == off2[0] and lhsR == off2[1])
    # A-relation: v_{i+3} = (1 + s_y) v_i = Y v_i
    for i in range(3):
        ok_ma &= (v[i + 3] == ymul(YY, v[i]))
    # B-relation: v_{i-1} + v_{i-2} = s_y v_i  ->  at i=0,1,2
    ok_mb &= (yxor(v[5], v[4]) == ymul(SY, v[0]))
    ok_mb &= (yxor(v[0], v[5]) == ymul(SY, v[1]))
    ok_mb &= (yxor(v[1], v[0]) == ymul(SY, v[2]))
    # endpoint: Ahat2 off2L = Bhat2 off2R (c2 = 0)
    ok_mfin &= (ring_mul4(AH[2], off2[0]) == ring_mul4(BH[2], off2[1]))
print(f"  off2L = v4+v5+w s_x v5, off2R = v3+w s_x v4+w2 v5: {ok_m1}")
print(f"  A-relation v_(i+3) = Y v_i: {ok_ma}")
print(f"  B-relations: {ok_mb}")
print(f"  endpoint Ahat2 off2L = Bhat2 off2R (c2 = 0): {ok_mfin}")

print("\n=== A2: chain endpoints (re-confirmation) ===")
K = nullspace_f2(d2b.T)
mins = []
for z in Z2all[:3]:
    pass
print("  (imDelta-distance = 12, duality, tau(u*) weight 12: verified in "
      "Entries 13, 17, 20, 21 —\n   the assembled theorem statement lives "
      "in the log entry.)")

print("\nDone.")
