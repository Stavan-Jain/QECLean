"""A3 / Track 1.1 Entries 11-12 — intermediates for the four remaining shape lemmas.

Machine-verification of every intermediate step in the hand proofs of
R-(2,1,1) [the D-pair lemma], R-(2,1,1,1), R-(2,2,1), R-(3,1,1) — the four
shape lemmas left open by Entry 10's six-shape architecture.  Conventions
follow `a3_mb_rigidity.py`: layers are indexed s in {0:[1], 1:[s_x], 2:[s_y],
3:[s_x s_y]}, cells t in Z3^2 with e = (0,1) the t_y unit, and the five
component characters psi_j given by ORBITS.  eta_j := psi_j((0,1)).

Checks:

  V1  C-table: the co-point ideal vector C_j(s4=[1]) = Ahat_j + Ahat_j[1]*uv
      has value pattern (0, eta_j, 1, eta_j^2) over (1, s_x, s_y, s_x s_y),
      i.e. C_j[s] = eta_j^{e(s)} with e = (-,1,0,2); psi_j((0,1)) = eta_j.
  V2  direction forcing: every weight-2 layer of a (2,1,1)- or (2,2,1)-shaped
      element of im(A.) has cell difference in the t_y direction {e, 2e};
      mirror for im(B.) (t_x direction).
  V3  R-(2,1,1) classification: the (2,1,1) elements of im(A.) are EXACTLY
      the 108 translates of the three predicted single-fibre patterns, and
      EXACTLY the 108 A-blocks of dA-pairs A.(delta_g + delta_{gd}), d in dA;
      dA cap dB = empty, |A.pair| = 4, |B.pair| = 6.
  V4  sharpened one-block lemma: for every z' in Ann(A) \ ker:
      V_0 = V_2 = V_4 = 0, V_3 in F4.uv (constant), V_1 in the ideal (Ahat_1);
      the hand case split (V_3 != 0 -> all four layers alive; V_1 support in
      {empty, co-point, full}) gives |Bz'| >= 16 in every case (exact min 16).
  V5  R-(2,1,1) endgame: for each dA-pair p, the completions z = p + z' with
      |Bz| <= 6 are exactly the 64 kernel translates (so b = the D-pair,
      |b| = 10); all other completions have |Bz| >= 10.
  V6  R-(3,1,1): every line kills >= 2 A-radical orbits; every non-collinear
      triple kills exactly one orbit class; triples whose dead orbit is the
      A-unit comp 2 always violate the consistency kappa_4 = kappa_1*kappa_3
      (9-case table, listed); hence im(A.) has NO (3,1,1) element (direct
      enumeration cross-check); mirror for im(B.).
  V7  R-(2,1,1,1): the (2,1,1,1) elements of im(A.) are exactly the 36
      translates of the predicted pattern {pair {t*+e, t*+2e} at one layer,
      deltas at t* on the other three}; completions: min |Bz| = 9 (no
      |Bz| = 5, so no |b| <= 10); the comp-1 transfer identity
      T := Ahat_1 * (1+u+v) has value vector C_1([1]) and T*uv = 0.
  V8  R-(2,2,1): the (2,2,1) elements of im(A.) are exactly the 108
      translates of the three predicted patterns (support inside a single
      t_y-fibre: {t}, {t,t+e}, {t,t+2e} distributed by the C-ratio rule);
      completions: min |Bz| = 9 (no |Bz| = 5, so no |b| <= 10).

Discovery/validation only; never load-bearing in a final analytic proof.
"""
from __future__ import annotations

from itertools import combinations, permutations, product

import numpy as np

from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.checks import bb_check_matrices
from bb_lab.linalg import nullspace_f2

Gb = ZmZn(6, 6)
Ab = Poly.from_string("x^3 + y + y^2", Gb)
Bb = Poly.from_string("y^3 + x + x^2", Gb)
cm = bb_check_matrices(Ab, Bb)
d2b = (cm.H_Z & 1).T
nb = 36
B_map, A_map = d2b[:nb, :], d2b[nb:, :]          # b = (B z | A z)

# ----------------------------------------------------------- F4 arithmetic
F4_MUL = np.zeros((4, 4), dtype=np.uint8)
for a in range(4):
    for b_ in range(4):
        a0, a1 = a & 1, a >> 1
        b0, b1 = b_ & 1, b_ >> 1
        c0 = (a0 & b0) ^ (a1 & b1)
        c1 = (a0 & b1) ^ (a1 & b0) ^ (a1 & b1)
        F4_MUL[a, b_] = c0 | (c1 << 1)
def f4mul(a, b): return int(F4_MUL[a, b])
def f4inv(a): return {1: 1, 2: 3, 3: 2}[a]
OMEGA = 2                                         # w; w^2 = 3; 1 + w = w^2

ORBITS = {0: (0, 0), 1: (0, 1), 2: (1, 0), 3: (1, 1), 4: (1, 2)}
def wpow(k): return [1, 2, 3][k % 3]
def psi(j, t):
    c, d = ORBITS[j]
    return wpow(c * (t // 3) + d * (t % 3))
ETA = {j: psi(j, 1) for j in (1, 3, 4)}           # psi_j((0,1)); t=(0,1) -> idx 1

def cell(tx, ty): return 3 * (tx % 3) + (ty % 3)
def cadd(t, u): return cell(t // 3 + u // 3, t % 3 + u % 3)
E, EX = cell(0, 1), cell(1, 0)                    # t_y and t_x units

def crt_idx(s, t):
    sx, sy = s & 1, (s >> 1) & 1
    tx, ty = t // 3, t % 3
    return Gb.index(((3 * sx + 4 * tx) % 6, (3 * sy + 4 * ty) % 6))
LAYER_CELLS = [[crt_idx(s, t) for t in range(9)] for s in range(4)]

def layers_of(f):
    return [frozenset(t for t in range(9) if f[LAYER_CELLS[s][t]]) for s in range(4)]

def vec_of(layer_sets):
    f = np.zeros(nb, np.uint8)
    for s, cells in enumerate(layer_sets):
        for t in cells:
            f[LAYER_CELLS[s][t]] = 1
    return f

def Vhat(f, j):
    """Component-j transform of a 36-vector, as a 4-vector over s-layers."""
    out = [0, 0, 0, 0]
    for s in range(4):
        for t in range(9):
            if f[LAYER_CELLS[s][t]]:
                out[s] ^= psi(j, t)
    return tuple(out)

def translate(f, dx, dy):
    out = np.zeros_like(f)
    for g in Gb:
        out[Gb.index(((g[0] + dx) % 6, (g[1] + dy) % 6))] = f[Gb.index(g)]
    return out

def all_translates(f):
    return {translate(f, dx, dy).tobytes() for dx in range(6) for dy in range(6)}

KA_dual = nullspace_f2(A_map.T)
KB_dual = nullspace_f2(B_map.T)
def in_imA(f): return not ((KA_dual @ f) % 2).any()
def in_imB(f): return not ((KB_dual @ f) % 2).any()

def enum_shape(shape, im_test):
    """All elements of the given image with the given layer-weight multiset."""
    out = set()
    for L in combinations(range(4), len(shape)):
        for ws in set(permutations(shape)):
            pools = [list(combinations(range(9), w)) for w in ws]
            for choice in product(*pools):
                f = np.zeros(nb, np.uint8)
                for s, T in zip(L, choice):
                    for t in T:
                        f[LAYER_CELLS[s][t]] = 1
                if im_test(f):
                    out.add(f.tobytes())
    return out

AnnA = nullspace_f2(A_map)
ker = nullspace_f2(d2b)
def span_list(rows):
    out = []
    for mask in range(1 << rows.shape[0]):
        v = np.zeros(rows.shape[1], np.uint8)
        for i in range(rows.shape[0]):
            if (mask >> i) & 1:
                v ^= rows[i]
        out.append(v)
    return out
AnnA_all = span_list(AnnA)
ker_set = {v.tobytes() for v in span_list(ker)}

def f2_solve(A, rhs):
    A = (A & 1).astype(np.uint8); rhs = (rhs & 1).astype(np.uint8)
    m, k = A.shape
    Aug = np.concatenate([A, rhs.reshape(-1, 1)], axis=1)
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
    return x

# Ahat_j value vectors over s-layers (from the lab's own column, as in G1).
delta0 = np.eye(nb, dtype=np.uint8)[Gb.index((0, 0))]
AH = {j: Vhat((A_map @ delta0) % 2, j) for j in range(5)}
BH = {j: Vhat((B_map @ delta0) % 2, j) for j in range(5)}

# ------------------------------------------------------------- V1: C-table
print("=== V1: C-table and eta normalizations ===")
ok = True
for j in (1, 3, 4):
    eta = ETA[j]
    ok &= (AH[j] == ((1 ^ eta), 1, eta, 0))      # (1+eta, 1, eta, 0)
    C = tuple(AH[j][s] ^ AH[j][0] for s in range(4))
    ok &= (C == (0, eta, 1, f4mul(eta, eta)))     # (0, eta, 1, eta^2)
    ok &= (f4mul(eta, eta) == (1 ^ eta))          # eta^2 = 1 + eta
print(f"  Ahat_j = (1+eta,1,eta,0); C_j([1]) = (0,eta,1,eta^2); eta^2 = 1+eta: {ok}")

# --------------------------------------------------- V2: direction forcing
print("\n=== V2: weight-2 layers of co-point shapes are t_y-pairs (A side) ===")
def pair_dirs(elems):
    dirs = set()
    for fb in elems:
        f = np.frombuffer(fb, dtype=np.uint8)
        for cells in layers_of(f):
            if len(cells) == 2:
                t1, t2 = sorted(cells)
                dirs.add(cadd(t2, cell(-(t1 // 3), -(t1 % 3))))
    return dirs

A211 = enum_shape((2, 1, 1), in_imA)
A221 = enum_shape((2, 2, 1), in_imA)
B211 = enum_shape((2, 1, 1), in_imB)
dirsA = pair_dirs(A211) | pair_dirs(A221)
dirsB = pair_dirs(B211)
print(f"  A-side pair differences: {sorted(dirsA)} (claim: subset of {{{E}, {cadd(E, E)}}} = t_y): "
      f"{dirsA <= {E, cadd(E, E)}}")
print(f"  B-side pair differences: {sorted(dirsB)} (claim: subset of {{{EX}, {cadd(EX, EX)}}} = t_x): "
      f"{dirsB <= {EX, cadd(EX, EX)}}")

# ------------------------------------------- V3: R-(2,1,1) classification
print("\n=== V3: (2,1,1) elements of im(A.) = predicted patterns = A.(dA-pairs) ===")
def pat211(sP, a):
    """Normalized pattern, zero layer [1]; pair at layer sP, base cell a."""
    L = [set(), set(), set(), set()]
    if sP == 2:
        L[1], L[2], L[3] = {a}, {a, cadd(a, E)}, {cadd(a, E)}
    elif sP == 1:
        L[1], L[2], L[3] = {a, cadd(a, E)}, {cadd(a, E)}, {a}
    else:
        L[1], L[2], L[3] = {cadd(a, E)}, {a}, {a, cadd(a, E)}
    return vec_of(L)

predicted = set()
for sP in (1, 2, 3):
    predicted |= all_translates(pat211(sP, 0))
dA = {((g1[0] - g2[0]) % 6, (g1[1] - g2[1]) % 6)
      for g1 in [(3, 0), (0, 1), (0, 2)] for g2 in [(3, 0), (0, 1), (0, 2)] if g1 != g2}
dB = {((g1[0] - g2[0]) % 6, (g1[1] - g2[1]) % 6)
      for g1 in [(0, 3), (1, 0), (2, 0)] for g2 in [(0, 3), (1, 0), (2, 0)] if g1 != g2}
dApairs, wts = set(), set()
for g in Gb:
    for d in dA:
        z = np.zeros(nb, np.uint8)
        z[Gb.index(g)] ^= 1
        z[Gb.index(((g[0] + d[0]) % 6, (g[1] + d[1]) % 6))] ^= 1
        dApairs.add(((A_map @ z) % 2).tobytes())
        wts.add((int(((A_map @ z) % 2).sum()), int(((B_map @ z) % 2).sum())))
print(f"  enumerated (2,1,1) in im(A.): {len(A211)}; predicted: {len(predicted)}; "
      f"A-blocks of dA-pairs: {len(dApairs)}")
print(f"  all three sets equal: {A211 == predicted == dApairs}")
print(f"  dA cap dB empty: {not (dA & dB)}; (|A.p|, |B.p|) for dA-pairs: {wts}")

# ------------------------------------------- V4: sharpened one-block lemma
print("\n=== V4: one-block structure and the >= 16 case analysis ===")
ideal_A1 = {tuple(f4mul(al, AH[1][s]) ^ be for s in range(4))
            for al in range(4) for be in range(4)}
ok_struct, ok_bound = True, True
case_mins = {}
for z in AnnA_all:
    if z.tobytes() in ker_set:
        continue
    Bz = (B_map @ z) % 2
    V = {j: Vhat(Bz, j) for j in range(5)}
    ok_struct &= V[0] == (0, 0, 0, 0) and V[2] == (0, 0, 0, 0) and V[4] == (0, 0, 0, 0)
    ok_struct &= len(set(V[3])) == 1                      # constant (possibly 0)
    ok_struct &= V[1] in ideal_A1
    n1 = sum(1 for x in V[1] if x)
    ok_struct &= n1 in (0, 3, 4)
    lay = layers_of(Bz)
    if any(V[3]):
        ok_struct &= all(len(c) > 0 for c in lay)         # V3 const != 0 -> all alive
    w = int(Bz.sum())
    key = (bool(any(V[3])), n1)
    case_mins[key] = min(case_mins.get(key, 99), w)
    ok_bound &= w >= 16
print(f"  V0=V2=V4=0, V3 constant, V1 in (Ahat_1) with support 0/3/4, "
      f"V3!=0 -> 4 layers alive: {ok_struct}")
print(f"  per-case (V3 alive?, |supp V1|) min |Bz'|: {dict(sorted(case_mins.items()))}")
print(f"  one-block min >= 16 in every case: {ok_bound}")

# --------------------------------------------------- V5: R-(2,1,1) endgame
print("\n=== V5: D-pair endgame (completions of dA-pairs) ===")
ok_end = True
for d in [(0, 1), (3, 1), (3, 2)]:
    z0 = np.zeros(nb, np.uint8)
    z0[Gb.index((0, 0))] = 1
    z0[Gb.index(d)] ^= 1
    Bp = (B_map @ z0) % 2
    n_light, n_ker, others_min = 0, 0, 99
    for z1 in AnnA_all:
        z = z0 ^ z1
        w = int(((B_map @ z) % 2).sum())
        if w <= 6:
            n_light += 1
            ok_end &= (((B_map @ z) % 2) == Bp).all()
        if z1.tobytes() in ker_set:
            n_ker += 1
        else:
            others_min = min(others_min, w)
    ok_end &= n_light == n_ker == 64
    print(f"  d = {d}: completions with |Bz| <= 6: {n_light} (= |ker| = 64), "
          f"all with Bz = Bp; min over non-ker: {others_min}")
print(f"  endgame verified for all three classes: {ok_end}")

# ----------------------------------------------------------- V6: R-(3,1,1)
print("\n=== V6: R-(3,1,1) — lines, triangles, and the kappa consistency ===")
ok_line = True
for g in (cell(1, 0), cell(0, 1), cell(1, 1), cell(1, 2)):
    line = [0, g, cadd(g, g)]
    dead = {j for j in (1, 3, 4) if not (psi(j, line[0]) ^ psi(j, line[1]) ^ psi(j, line[2]))}
    ok_line &= len(dead) >= 2
print(f"  every line through 0 kills >= 2 A-radical orbits: {ok_line}")
ok_tri, ok_kappa, table = True, True, []
for g in range(1, 9):
    for h in range(1, 9):
        if h == g or cadd(g, g) == h:                     # h = 2g <=> collinear
            continue
        kap = {j: 1 ^ psi(j, g) ^ psi(j, h) for j in (1, 2, 3, 4)}
        dead = {j for j, v in kap.items() if v == 0}
        ok_tri &= len(dead) == 1
        if dead == {2}:
            consistent = f4mul(kap[1], kap[3]) == kap[4]
            ok_kappa &= not consistent
            if (g // 3, g % 3) < (h // 3, h % 3):
                table.append(((g // 3, g % 3), (h // 3, h % 3),
                              kap[1], kap[3], kap[4], f4mul(kap[1], kap[3])))
ok_tri_all = ok_tri
print(f"  every non-collinear triple kills exactly one orbit class: {ok_tri_all}")
print(f"  dead-orbit-2 triples all violate kappa4 = kappa1*kappa3: {ok_kappa}")
print(f"  ({len(table)} unordered dead-orbit-2 cases; F4 codes 1/2/3 = 1/w/w^2)")
for row in table:
    print(f"    g={row[0]} h={row[1]}: kappa1={row[2]} kappa3={row[3]} "
          f"kappa4={row[4]} != kappa1*kappa3={row[5]}")
A311 = enum_shape((3, 1, 1), in_imA)
B311 = enum_shape((3, 1, 1), in_imB)
print(f"  direct enumeration: (3,1,1) in im(A.): {len(A311)}; in im(B.): {len(B311)} "
      f"(claim: 0, 0)")

# --------------------------------------------------------- V7: R-(2,1,1,1)
print("\n=== V7: R-(2,1,1,1) — classification, completions, comp-1 identity ===")
def swap_vec(f):
    out = np.zeros_like(f)
    for g in Gb:
        out[Gb.index((g[1], g[0]))] = f[Gb.index(g)]
    return out

A2111 = enum_shape((2, 1, 1, 1), in_imA)
pat = vec_of([{cadd(0, E), cadd(0, cadd(E, E))}, {0}, {0}, {0}])
pred = all_translates(pat)
print(f"  enumerated (2,1,1,1) in im(A.): {len(A2111)}; predicted translates: {len(pred)}; "
      f"equal: {A2111 == pred}")
B2111 = enum_shape((2, 1, 1, 1), in_imB)
ok_mirror = B2111 == {swap_vec(np.frombuffer(fb, dtype=np.uint8)).tobytes() for fb in A2111}
print(f"  (2,1,1,1) in im(B.) = swap of the A-side classification: {ok_mirror}")
z0 = f2_solve(A_map, pat)
ws = sorted({int(((B_map @ (z0 ^ z1)) % 2).sum()) for z1 in AnnA_all})
print(f"  completion |Bz| values: min = {ws[0]} (claim 9; in particular never 5)")

def ring_mul(f, g):
    out = [0, 0, 0, 0]
    for s1 in range(4):
        for s2 in range(4):
            out[s1 ^ s2] ^= f4mul(f[s1], g[s2])
    return tuple(out)
Bunit_inv = (1, 1, 1, 0)                                  # 1+u+v = (1,1,1,0); self-inverse
ok_T = ring_mul(Bunit_inv, Bunit_inv) == (1, 0, 0, 0)
T = ring_mul(AH[1], Bunit_inv)
C1 = tuple(AH[1][s] ^ AH[1][0] for s in range(4))
ok_T &= (T == C1) and ring_mul(T, (1, 1, 1, 1)) == (0, 0, 0, 0)
print(f"  (1+u+v)^2 = 1, T := Ahat_1*(1+u+v) = C_1([1]) = {T}, T*uv = 0: {ok_T}")

# ----------------------------------------------------------- V8: R-(2,2,1)
print("\n=== V8: R-(2,2,1) — classification and completions ===")
def pat221(sD, t):
    L = [set(), set(), set(), set()]
    others = [s for s in (1, 2, 3) if s != sD]
    cval = {1: ETA[1], 2: 1, 3: f4mul(ETA[1], ETA[1])}    # C-values (eta,1,eta^2)
    L[sD] = {t}
    for s in others:
        k = next(k for k in (1, 2) if
                 f4mul(cval[s], [1, ETA[1], f4mul(ETA[1], ETA[1])][k]) == cval[sD])
        L[s] = {t, cadd(t, E if k == 1 else cadd(E, E))}
    return vec_of(L)

pred221 = set()
for sD in (1, 2, 3):
    pred221 |= all_translates(pat221(sD, 0))
print(f"  enumerated (2,2,1) in im(A.): {len(A221)}; predicted: {len(pred221)}; "
      f"equal: {A221 == pred221}")
ok_mirror221 = enum_shape((2, 2, 1), in_imB) == {
    swap_vec(np.frombuffer(fb, dtype=np.uint8)).tobytes() for fb in A221}
print(f"  (2,2,1) in im(B.) = swap of the A-side classification: {ok_mirror221}")
ok_fibre = True
for fb in A221:
    f = np.frombuffer(fb, dtype=np.uint8)
    cells = set().union(*layers_of(f))
    ok_fibre &= len({t // 3 for t in cells}) == 1         # single t_y-fibre
print(f"  every (2,2,1) element supported on a single t_y-fibre: {ok_fibre}")
mins = set()
for sD in (1, 2, 3):
    z0 = f2_solve(A_map, pat221(sD, 0))
    mins.add(min(int(((B_map @ (z0 ^ z1)) % 2).sum()) for z1 in AnnA_all))
print(f"  completion min |Bz| per class: {sorted(mins)} (claim: 9; never 5)")

print("\nDone.")
