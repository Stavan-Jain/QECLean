"""A3 / Track 1.1 Entry 16 — the safe-sector (M)-analogue: foundations + discovery.

Goal 1 (d(gross) = 12) reduces to the safe-sector mirror of (M): for every
base 1-cycle w with [w] != 0,

    (M-safe):  |w| + 2*m_safe(w) >= 12,
    m_safe(w) := min{ |v0 off supp w| : d1 v0 = d1c_j w }   (any cut j),

because a cover cycle v = (v0, v1) with p(v) = w satisfies (block algebra)
d1 v0 = d1c_j w and |v| = |w| + 2*|v0 off supp w|.  This script verifies the
framework and scans the light rungs.

  S1  cover block form: H_X^cov = [[d1nc_j, d1c_j], [d1c_j, d1nc_j]] in
      sheet coordinates, for every cut j (re-derivation, independent of
      a3_cut_decomposition.py).
  S2  safe parametrization: for sample logicals w, the map v0 -> (v0, v0+w)
      is a bijection {d1 v0 = d1c_j w} <-> {cover cycles v : p(v) = w};
      solvability is cut-independent; |v| = |w| + 2|v0 off w| pointwise.
  S3  base cycles have even weight (augmentation), so the light rungs are
      |w| in {6, 8, 10} with m_safe >= 3, 2, 1 resp.
  S4  weight-6 cycle census by split type (a, b) = (|u_L|, |u_R|):
      expected (6,0): 36 Ann(A)-type, (0,6): 36 Ann(B)-type, (3,3): 36
      hexagons (trivial class) + the remaining logicals; orbit structure
      of the 84 logicals under translation; class-spread over H_1.
  S5  m_safe for representatives of each weight-6 logical orbit, by exact
      T-enumeration (inside-syndrome dictionary + off-support tails up to
      weight 5); cut-independence and translation-covariance checks.
      Expected value 4 (the safe slice minimum 14 = 6 + 2*4 implied by the
      SAT facts d = 12 + all weight-12 minimizers dangerous + evenness).
  S6  structure of the Ann-type logicals: single t_y-fibre, shape (2,2,2)
      with t_y-direction pairs, x-span {c, c+3} (both columns of the
      fibre) — the inputs to the Entry-16 hand classification and to the
      seam-crossing obligation (s_j(w) != 0 for every cut).

Discovery/validation only; never load-bearing in a final analytic proof.
"""
from __future__ import annotations

from itertools import combinations

import numpy as np

from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.checks import bb_check_matrices
from bb_lab.linalg import nullspace_f2, rank_f2

Gb = ZmZn(6, 6)
Ab = Poly.from_string("x^3 + y + y^2", Gb)
Bb = Poly.from_string("y^3 + x + x^2", Gb)
cmb = bb_check_matrices(Ab, Bb)
HX = (cmb.H_X & 1)
HZ = (cmb.H_Z & 1)
d2b = HZ.T
nb = 36

Gc = ZmZn(12, 6)
Ac = Poly.from_string("x^3 + y + y^2", Gc)
Bc = Poly.from_string("y^3 + x + x^2", Gc)
cmc = bb_check_matrices(Ac, Bc)
HXc = (cmc.H_X & 1)
nc_ = 72

# Monomial x-degrees for the c/nc split: column g of M_P has checks p*g.
A_steps = [(3, 0), (0, 1), (0, 2)]
B_steps = [(0, 3), (1, 0), (2, 0)]

def split_cut(j):
    """Base d1 = (M_A | M_B) split into non-crossing/crossing parts at cut j
    (fundamental x-window {j..j+5}; a step from x crosses iff
    (x - j) mod 6 + step_x >= 6)."""
    d1nc = np.zeros((nb, 2 * nb), np.uint8)
    d1c = np.zeros((nb, 2 * nb), np.uint8)
    for blk, steps in ((0, A_steps), (1, B_steps)):
        for g in Gb:
            col = blk * nb + Gb.index(g)
            for (sx, sy) in steps:
                chk = Gb.index(((g[0] + sx) % 6, (g[1] + sy) % 6))
                tgt = d1c if ((g[0] - j) % 6) + sx >= 6 else d1nc
                tgt[chk, col] ^= 1
    return d1nc, d1c

def split_d2(j, z):
    """(d2nc_j z, d2c_j z) for a 2-chain z: left block B-steps, right A-steps."""
    out_nc = np.zeros(72, np.uint8)
    out_c = np.zeros(72, np.uint8)
    for g in Gb:
        if not z[Gb.index(g)]:
            continue
        for blk, steps in ((0, B_steps), (1, A_steps)):
            for (sx, sy) in steps:
                cell = blk * nb + Gb.index(((g[0] + sx) % 6, (g[1] + sy) % 6))
                tgt = out_c if ((g[0] - j) % 6) + sx >= 6 else out_nc
                tgt[cell] ^= 1
    return out_nc, out_c

# ----------------------------------------------------------- S1: block form
print("=== S1: cover block form vs base c/nc split (all 6 cuts) ===")
# Sheet coordinates at cut j: sheet 0 = x-window {j..j+5} of the cover,
# sheet 1 = {j+6..j+11}; base projection x mod 6.
ok_s1 = True
for j in range(6):
    d1nc, d1c = split_cut(j)
    # build the permuted cover matrix in sheet coords
    qmap = {}                                     # (sheet, blk, base g) -> cover col
    for blk in range(2):
        for gx in range(12):
            for gy in range(6):
                col = blk * nc_ + Gc.index((gx, gy))
                sheet = 0 if (gx - j) % 12 < 6 else 1
                qmap[(sheet, blk, ((gx % 6), gy))] = col
    cmapn = {}
    for cx in range(12):
        for cy in range(6):
            row = Gc.index((cx, cy))
            sheet = 0 if (cx - j) % 12 < 6 else 1
            cmapn[(sheet, ((cx % 6), cy))] = row
    for sc in range(2):                           # check sheet
        for sq in range(2):                       # qubit sheet
            # extract: rows = base checks in sheet sc, cols = base qubits in sheet sq
            M = np.zeros((nb, 2 * nb), np.uint8)
            for blk in range(2):
                for g in Gb:
                    colb = blk * nb + Gb.index(g)
                    colc = qmap[(sq, blk, g)]
                    for c in Gb:
                        M[Gb.index(c), colb] = HXc[cmapn[(sc, c)], colc]
            ok_s1 &= (M == (d1nc if sc == sq else d1c)).all()
print(f"  H_X^cov = [[nc_j, c_j], [c_j, nc_j]] for every cut j: {ok_s1}")

# -------------------------------------------------- helper: logical census
kerHX = nullspace_f2(HX)                          # dim 42
B1 = d2b.T                                        # rows span im d2 (as vectors)
def in_imd2(w):
    return rank_f2(np.vstack([d2b.T, w])) == rank_f2(d2b.T)
rank_B1 = rank_f2(d2b.T)
# class functionals: X-logical basis = ker H_Z reduced against rowspace H_X
kerHZ = nullspace_f2(HZ)
L_rows = []
acc = HX.copy()
r0 = rank_f2(acc)
for v in kerHZ:
    test = np.vstack([acc, v])
    r1 = rank_f2(test)
    if r1 > r0:
        L_rows.append(v)
        acc, r0 = test, r1
L = np.array(L_rows, np.uint8)                    # 12 x 72
print(f"\n  class functionals: {L.shape[0]} (claim 12)")

def col_ints(M):
    return [int("".join(str(b) for b in M[:, i]), 2) for i in range(M.shape[1])]

def syndromes(M, k):
    cols = col_ints(M)
    out = {}
    def rec(start, depth, acc, cells):
        if depth == k:
            out.setdefault(acc, []).append(tuple(cells))
            return
        for i in range(start, len(cols) - (k - depth - 1)):
            cells.append(i)
            rec(i + 1, depth + 1, acc ^ cols[i], cells)
            cells.pop()
    rec(0, 0, 0, [])
    return out

MA, MB = HX[:, :nb], HX[:, nb:]

# ------------------------------------------------ S4: weight-6 cycle census
print("\n=== S4: weight-6 cycles by split; logical orbits; class spread ===")
def span_elems(rows):
    out = []
    for mask in range(1 << rows.shape[0]):
        v = np.zeros(rows.shape[1], np.uint8)
        for i in range(rows.shape[0]):
            if (mask >> i) & 1:
                v ^= rows[i]
        out.append(v)
    return out
AnnA6 = [z for z in span_elems(nullspace_f2(d2b[nb:, :])) if z.sum() == 6]
AnnB6 = [z for z in span_elems(nullspace_f2(d2b[:nb, :])) if z.sum() == 6]
print(f"  Ann(A) weight-6 elements: {len(AnnA6)}; Ann(B): {len(AnnB6)} (claim 36 + 36)")

SA = {k: syndromes(MA, k) for k in (1, 2, 3, 4, 5)}
SB = {k: syndromes(MB, k) for k in (1, 2, 3, 4, 5)}
w6 = []
for a in range(0, 7):
    b = 6 - a
    cnt = 0
    if a == 0:
        for z in AnnB6:
            w = np.zeros(72, np.uint8); w[nb:] = z
            w6.append(w); cnt += 1
    elif b == 0:
        for z in AnnA6:
            w = np.zeros(72, np.uint8); w[:nb] = z
            w6.append(w); cnt += 1
    else:
        common = set(SA[a]) & set(SB[b])
        for s in common:
            for TL in SA[a][s]:
                for TR in SB[b][s]:
                    w = np.zeros(72, np.uint8)
                    for i in TL:
                        w[i] = 1
                    for i in TR:
                        w[nb + i] = 1
                    w6.append(w); cnt += 1
    if cnt:
        print(f"  split ({a},{b}): {cnt} cycles")
print(f"  total weight-6 cycles: {len(w6)} (claim 120)")

def translate72(w, dx, dy):
    out = np.zeros_like(w)
    for blk in range(2):
        for g in Gb:
            out[blk * nb + Gb.index(((g[0] + dx) % 6, (g[1] + dy) % 6))] = \
                w[blk * nb + Gb.index(g)]
    return out

logicals6, hexes = [], 0
for w in w6:
    if in_imd2(w):
        hexes += 1
    else:
        logicals6.append(w)
print(f"  stabilizers among them: {hexes} (claim 36 hexagons); logicals: {len(logicals6)}")
orbits = {}
for w in logicals6:
    canon = min(translate72(w, dx, dy).tobytes() for dx in range(6) for dy in range(6))
    orbits.setdefault(canon, []).append(w)
print(f"  translation orbits of the 84 logicals: {len(orbits)} "
      f"with sizes {sorted(len(v) for v in orbits.values())}")
classes = {}
for w in logicals6:
    cid = tuple((L @ w) % 2)
    classes.setdefault(cid, 0)
    classes[cid] += 1
print(f"  distinct H1 classes among weight-6 logicals: {len(classes)}; "
      f"per-class counts: {sorted(set(classes.values()))}")

# ----------------------------------------------- S2/S3: safe parametrization
print("\n=== S2/S3: safe-slice algebra on samples ===")
rng = np.random.default_rng(7)
def d1c_apply(j, w):
    _, d1c = split_cut(j)
    return (d1c @ w) % 2
def f2_solve(Amat, rhs):
    Amat = (Amat & 1).astype(np.uint8); rhs = (rhs & 1).astype(np.uint8)
    m, k = Amat.shape
    Aug = np.concatenate([Amat, rhs.reshape(-1, 1)], axis=1)
    piv_row = 0; piv_cols = []
    for col in range(k):
        nz = np.flatnonzero(Aug[piv_row:, col])
        if nz.size == 0:
            continue
        r = piv_row + int(nz[0])
        if r != piv_row:
            Aug[[piv_row, r]] = Aug[[r, piv_row]]
        msk = Aug[:, col] == 1; msk[piv_row] = False
        if msk.any():
            Aug[msk] ^= Aug[piv_row]
        piv_cols.append(col); piv_row += 1
        if piv_row == m:
            break
    x = np.zeros(k, np.uint8)
    for i, col in enumerate(piv_cols):
        x[col] = Aug[i, k]
    if ((Amat @ x) % 2 != rhs).any():
        return None
    return x

def lift_to_cover(j, v0, v1):
    """Place sheet chains (v0, v1) at cut j into a cover vector."""
    v = np.zeros(2 * nc_, np.uint8)
    for blk in range(2):
        for g in Gb:
            for sheet, vs in ((0, v0), (1, v1)):
                off = (g[0] - j) % 6
                cx = (j + off + (6 if sheet else 0)) % 12
                v[blk * nc_ + Gc.index((cx, g[1]))] ^= vs[blk * nb + Gb.index(g)]
    return v

ok_s2 = True
samples = [logicals6[0], logicals6[40], logicals6[-1]]
for w in samples:
    sols = {}
    for j in range(6):
        s = d1c_apply(j, w)
        v0 = f2_solve(HX, s)
        sols[j] = v0
    ok_s2 &= len({v0 is None for v0 in sols.values()}) == 1   # solvability cut-indep
    j = 0
    if sols[j] is not None:
        for _ in range(20):
            c = np.zeros(72, np.uint8)
            for i in rng.choice(len(kerHX), 5, replace=False):
                c ^= kerHX[i]
            v0 = sols[j] ^ c
            v = lift_to_cover(j, v0, v0 ^ w)
            ok_s2 &= not ((HXc @ v) % 2).any()                # cover cycle
            off = int(v0[np.asarray(w) == 0].sum())
            ok_s2 &= int(v.sum()) == int(w.sum()) + 2 * off   # weight identity
print(f"  solvability cut-independent; v0-solutions lift to cover cycles; "
      f"|v| = |w| + 2|v0 off w|: {ok_s2}")
evens = all(int(w.sum()) % 2 == 0 for w in w6)
print(f"  S3: all sampled cycles even (augmentation argument): {evens}")

# ------------------------------------------------------------ S5: m_safe
print("\n=== S5: m_safe for weight-6 logical orbit representatives ===")
hx_cols = col_ints(HX)
def m_safe(w, j, mmax=5):
    s_vec = d1c_apply(j, w)
    if f2_solve(HX, s_vec) is None:
        return None                                # slice empty (w unreachable)
    s = int("".join(str(b) for b in s_vec), 2)
    supp = [i for i in range(72) if w[i]]
    comp = [i for i in range(72) if not w[i]]
    inside = {}
    for r in range(len(supp) + 1):
        for P in combinations(supp, r):
            acc = 0
            for i in P:
                acc ^= hx_cols[i]
            inside[acc] = True
    if s in inside:
        return 0
    for m in range(1, mmax + 1):
        for T in combinations(comp, m):
            acc = s
            for i in T:
                acc ^= hx_cols[i]
            if acc in inside:
                return m
    return mmax + 1                                # ">= mmax+1"

reps = [np.frombuffer(k, dtype=np.uint8).copy() for k in sorted(orbits)]
for idx, w in enumerate(reps):
    cuts = range(6) if idx < 2 else (0,)
    vals = [m_safe(w, j, mmax=4) for j in cuts]
    if vals[0] is None:
        print(f"  orbit rep {idx} (split {int(w[:nb].sum())},{int(w[nb:].sum())}): "
              f"slice EMPTY (class outside im pr_*; rung vacuous)")
        continue
    tag = "cuts agree" if len(set(vals)) == 1 else f"VALUES DIFFER {vals}"
    v = vals[0]
    shown = f"{v}" if v <= 4 else ">=5"
    print(f"  orbit rep {idx} (split {int(w[:nb].sum())},{int(w[nb:].sum())}): "
          f"m_safe = {shown} ({tag})")
w0 = reps[0]
wt = translate72(w0, 2, 3)
print(f"  translation covariance (rep 0 shifted by (2,3)): "
      f"m_safe = {m_safe(wt, 0, mmax=4)}")

# ------------------------------------------------- S6: Ann-type structure
print("\n=== S6: structure of Ann(A)-type weight-6 logicals ===")
def crt_idx(s, t):
    sx, sy = s & 1, (s >> 1) & 1
    tx, ty = t // 3, t % 3
    return Gb.index(((3 * sx + 4 * tx) % 6, (3 * sy + 4 * ty) % 6))
LAYER_CELLS = [[crt_idx(s, t) for t in range(9)] for s in range(4)]
ok_s6 = True
for z in AnnA6:
    lays = [sorted(t for t in range(9) if z[LAYER_CELLS[s][t]]) for s in range(4)]
    sizes = sorted(len(l) for l in lays)
    ok_s6 &= sizes == [0, 2, 2, 2]
    cells = [(g[0], g[1]) for g in Gb if z[Gb.index(g)]]
    txs = {x % 3 for (x, y) in cells}
    ok_s6 &= len(txs) == 1                         # single t_y-fibre
    xs = {x for (x, y) in cells}
    ok_s6 &= len(xs) == 2 and (max(xs) - min(xs)) % 6 == 3   # x-span {c, c+3}
    for l in lays:
        if len(l) == 2:
            t1, t2 = l
            ok_s6 &= (t1 // 3) == (t2 // 3)        # t_y-direction pair
print(f"  every Ann(A)-wt-6 element: shape (2,2,2), single fibre, t_y-pairs, "
      f"x-span {{c, c+3}}: {ok_s6}")
print(f"  z* = {[g for g in Gb if AnnA6[0][Gb.index(g)]] if AnnA6 else None} (sample)")

# -------------------------------------- S7: ker(delta) = im(Delta) question
print("\n=== S7: reachable classes (ker delta) vs the Smith classes (im Delta) ===")
K0 = nullspace_f2(HX.T)                            # coker d1 functionals (6)
print(f"  coker d1 dimension: {K0.shape[0]} (claim 6)")
# H1 basis: 12 cycles independent mod im d2
H1_reps = []
acc = d2b.T.copy()
r0 = rank_f2(acc)
for v in kerHX:
    test = np.vstack([acc, v])
    r1 = rank_f2(test)
    if r1 > r0:
        H1_reps.append(v)
        acc, r0 = test, r1
H1_reps = np.array(H1_reps, np.uint8)
print(f"  H1 basis size: {H1_reps.shape[0]} (claim 12)")

def class_vec(w):
    return tuple((L @ w) % 2)

ok_s7 = True
kerdelta_sets, imdelta_sets = [], []
ker2 = nullspace_f2(d2b)                           # H2 basis (6)
for j in range(6):
    _, d1c = split_cut(j)
    D = np.array([(K0 @ ((d1c @ w) % 2)) % 2 for w in H1_reps], np.uint8).T  # 6x12
    kerD = nullspace_f2(D)                         # coefficient vectors c with Dc = 0
    reach = set()
    for mask in range(1 << kerD.shape[0]):
        c = np.zeros(12, np.uint8)
        for i in range(kerD.shape[0]):
            if (mask >> i) & 1:
                c ^= kerD[i]
        w = np.zeros(72, np.uint8)
        for i in range(12):
            if c[i]:
                w ^= H1_reps[i]
        reach.add(class_vec(w))
    kerdelta_sets.append(frozenset(reach))
    imd = set()
    for mask in range(1 << ker2.shape[0]):
        z = np.zeros(36, np.uint8)
        for i in range(ker2.shape[0]):
            if (mask >> i) & 1:
                z ^= ker2[i]
        # the Smith rep of Delta[z] is the 1-chain d2c_j z; build it as a cycle
        # via the d2 split: d2c_j z is a cycle (chain identities), class via L
        d2nc_, d2c_ = split_d2(j, z)
        imd.add(class_vec(d2c_))
    imdelta_sets.append(frozenset(imd))
ok_s7 &= len(set(kerdelta_sets)) == 1 and len(set(imdelta_sets)) == 1
print(f"  ker(delta) cut-independent: {len(set(kerdelta_sets)) == 1}; "
      f"im(Delta) cut-independent: {len(set(imdelta_sets)) == 1}")
print(f"  |ker delta| = {len(kerdelta_sets[0])}; |im Delta| = {len(imdelta_sets[0])} "
      f"(claims 64, 64; Delta injective: {len(imdelta_sets[0]) == 64})")
print(f"  ker(delta) == im(Delta) as class sets: "
      f"{kerdelta_sets[0] == imdelta_sets[0]}")
w6cls = {class_vec(w) for w in logicals6}
print(f"  weight-6 logical classes inside ker(delta): "
      f"{len(w6cls & kerdelta_sets[0])} (claim 0 — all unreachable)")

# ------------------------------------------------------- S8: the zeta side
print("\n=== S8: ker d2 and the Smith representatives d2c_j zeta ===")
wts = {}
for mask in range(1 << ker2.shape[0]):
    z = np.zeros(36, np.uint8)
    for i in range(ker2.shape[0]):
        if (mask >> i) & 1:
            z ^= ker2[i]
    wts.setdefault(int(z.sum()), 0)
    wts[int(z.sum())] += 1
print(f"  ker d2 weight enumerator: {dict(sorted(wts.items()))}")
rep_wts = {}
for mask in range(1, 1 << ker2.shape[0]):
    z = np.zeros(36, np.uint8)
    for i in range(ker2.shape[0]):
        if (mask >> i) & 1:
            z ^= ker2[i]
    _, d2c_ = split_d2(0, z)
    rep_wts.setdefault(int(d2c_.sum()), 0)
    rep_wts[int(d2c_.sum())] += 1
print(f"  |d2c_0 zeta| distribution over the 63 nonzero zeta: "
      f"{dict(sorted(rep_wts.items()))}")
print("  (class minima over im Delta: 12, by the C2 crosscheck — SAT, discovery only)")

print("\nDone.")
