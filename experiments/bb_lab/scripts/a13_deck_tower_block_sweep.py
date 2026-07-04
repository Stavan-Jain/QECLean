"""A13 screens: deck-trivial <=> k-constant along Z_{2^r} doubling towers.

Adversarial verification of the (draft) Theorem A13 and of every internal
step of its proof, at the CRT-block level. Blocks T = S[P] (S = F_{2^d},
P = 2-part of the tower-top group) with a deck element s in P of order
N = 2^r >= 4, eps = 1 + s, so T is free over F2[eps]/(eps^N) and
Ann(eps^j) = eps^(N-j) T.

Per pair (A, B) in T^2 the script checks, with I = (A,B):

  S1  (R) <=> eps in I            [(R) = eps * H1 = 0; the A13 endpoint]
  S2  k-profile k_j = 2 dim T/(I + eps^{2^j}) monotone; k_r = k_0 <=> eps in I
  S0  rank d2 = rank d1           [Lemma 0 / Frobenius, internal sanity]
  S3  if eps not in I and 2 <= t* <= N-2 (t* = min t with eps^t in I):
      the canonical violator z* = eps^{N-t*}(f,g)  [eps^{t*} = fA + gB]
      is a cycle and eps z* is NOT a boundary      [proof mechanism]
  S7  same regime: the divided class is eps-alive: eps(f,g) is NOT a
      level-t* boundary                            [liveness bootstrap]
  S4  if eps not in I and t* >= N-1: eps^{N/2} not in I and the top-step
      deck eps^{N/2} acts nontrivially on H1       [A12 block regression]
  S5  R3 divided-class lemma (heavy, subsampled): whenever eps^u in I
      with witness (f,g), the level-u cycles are exactly
      p(top cycles) + T*(f,g) + eps^u T^2
  S6  if eps in I (subsampled): level-u divided class dies (Ob = 0)
  S8  Lemma-0 at level u (heavy, subsampled): direct dim H1(level) agrees
      with 2 dim T/(I + eps^u T)

Any S1/S2/S0 violation is a counterexample to the theorem (or a bug in
the derivation); S3/S7 violations break the proof mechanism even if the
endpoint survives. Everything is expected ALL-PASS.

Coverage: exhaustive for F2[Z4] (N=4), F2[Z8] (N=4 and N=8), F4[Z4]
(N=4), F2[Z4xZ2] (N=4, both deck classes); sampled (uniform + a targeted
stratum forcing eps^2 in I) for F2[Z8xZ2] (N=4, N=8), F2[Z4xZ4],
F4[Z4xZ2]. F8 blocks remain out of scope (BlockAlgebra supports d<=2),
same residual gap as the A12 sweep.

Run: python3 scripts/a13_deck_tower_block_sweep.py   (from experiments/bb_lab)
"""

import itertools
import os
import random
import sys
import time
from math import gcd

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from a12_bockstein_block_sweep import BlockAlgebra, nullspace, rref_add  # noqa: E402


# ---------- small F2 helpers on top of the a12 machinery ----------

def span_basis(vectors):
    basis = []
    for v in vectors:
        rref_add(basis, v)
    return basis


def reduce_span(basis, v):
    for b in basis:
        v = min(v, v ^ b)
    return v


def in_span(basis, v):
    return reduce_span(basis, v) == 0


def apply_cols(cols, v):
    """Apply the linear map with the given columns to the bitmask v."""
    w = 0
    while v:
        b = v & -v
        v ^= b
        w ^= cols[b.bit_length() - 1]
    return w


def solve(cols, target):
    """Solve sum_{j in combo} cols[j] = target; return combo mask or None.

    Forward elimination; each pivot is reduced against all earlier pivots,
    so its low bit never reappears (single reduction pass is sound)."""
    piv = []
    for j, c in enumerate(cols):
        comb = 1 << j
        for pv, pc in piv:
            if c & (pv & -pv):
                c ^= pv
                comb ^= pc
        if c:
            piv.append((c, comb))
    t, tc = target, 0
    for pv, pc in piv:
        if t & (pv & -pv):
            t ^= pv
            tc ^= pc
    return tc if t == 0 else None


def apply_eps_c1(eps_cols, n, v):
    """eps acting blockwise on C1 = T^2 (v is a 2n-bit mask)."""
    w = 0
    low = v
    while low:
        b = low & -low
        c = b.bit_length() - 1
        low ^= b
        if c < n:
            w ^= eps_cols[c]
        else:
            w ^= eps_cols[c - n] << n
    return w


def elt_order(pa, pb, i, j):
    oa = pa // gcd(i, pa) if i else 1
    ob = pb // gcd(j, pb) if j else 1
    return oa * ob // gcd(oa, ob)


# ---------- per-pair battery ----------

class DeckData:
    """Precomputed data for (block algebra, deck element s of order N)."""

    def __init__(self, alg, s_ij, N):
        self.alg, self.s_ij, self.N = alg, s_ij, N
        n = alg.n
        one = 1 << alg.coord(0, alg.pidx(0, 0))
        eps = one | (1 << alg.coord(0, alg.pidx(*s_ij)))
        self.eps = eps
        self.eps_cols = alg.elt_matrix(eps)
        # eps powers as elements, eps_pow[0] = 1
        self.eps_pow = [one]
        for _ in range(N):
            self.eps_pow.append(apply_cols(self.eps_cols, self.eps_pow[-1]))
        assert self.eps_pow[N] == 0, "eps^N != 0: deck order wrong"
        assert self.eps_pow[N - 1] != 0, "eps^(N-1) = 0: not free over Lambda"
        # multiplication matrices of eps powers (for the violator check)
        self.epow_mats = [alg.elt_matrix(self.eps_pow[t]) for t in range(N)]
        # F2-span of eps^u T for each u (level subspaces W_u)
        self.W = [span_basis(self.epow_mats[t]) for t in range(N)]

    def r_of(self):
        return self.N.bit_length() - 1


class Tally:
    def __init__(self):
        self.pairs = 0
        self.geography = {}          # (R, memb) -> count
        self.tstar_hist = {}         # t* histogram over eps-not-in-I pairs
        self.ob_alive = 0            # S7 confirmations
        self.violator_fired = 0      # S3 confirmations
        self.a12_regressions = 0     # S4 confirmations
        self.heavy_r3 = 0
        self.heavy_s6 = 0
        self.heavy_s8 = 0
        self.violations = []         # (tag, A, B, detail)


def check_pair(dd, A, B, tally, heavy_budget):
    alg, N = dd.alg, dd.N
    n = alg.n
    MA = alg.elt_matrix(A)
    MB = alg.elt_matrix(B)
    d1_cols = MA + MB

    ideal = span_basis(d1_cols)
    rank_d1 = len(ideal)
    memb = in_span(ideal, dd.eps)

    # t* = min t with eps^t in I  (eps^N = 0 is always in I)
    tstar = N
    for t in range(N):
        if in_span(ideal, dd.eps_pow[t]):
            tstar = t
            break

    # (R): eps kills H1
    ker = nullspace(d1_cols, n)
    im2 = []
    for h in range(n):
        rref_add(im2, MB[h] | (MA[h] << n))
    rank_d2 = len(im2)
    R_holds = True
    for v in ker:
        if not in_span(im2, apply_eps_c1(dd.eps_cols, n, v)):
            R_holds = False
            break

    tally.pairs += 1
    tally.geography[(R_holds, memb)] = \
        tally.geography.get((R_holds, memb), 0) + 1

    # S0: Lemma 0 (rank d2 = rank d1, Frobenius duality)
    if rank_d2 != rank_d1:
        tally.violations.append(("S0", A, B, f"rank d1={rank_d1} d2={rank_d2}"))

    # S1: the A13 endpoint
    if R_holds != memb:
        tally.violations.append(
            ("S1-COUNTEREXAMPLE", A, B, f"R={R_holds} memb={memb} t*={tstar}"))
        return  # everything downstream is moot for this pair

    # S2: k-profile via the counting lemma (Lemma 0 per level)
    r = dd.r_of()
    kprof = []
    for j in range(r + 1):
        u = min(1 << j, N)
        lev = list(ideal)
        for c in dd.epow_mats[u] if u < N else []:
            rref_add(lev, c)
        kprof.append(2 * (n - len(lev)))
    if any(kprof[j] > kprof[j + 1] for j in range(r)):
        tally.violations.append(("S2-monotone", A, B, str(kprof)))
    if (kprof[r] == kprof[0]) != memb:
        tally.violations.append(("S2-count", A, B, f"{kprof} memb={memb}"))

    if not memb:
        tally.tstar_hist[tstar] = tally.tstar_hist.get(tstar, 0) + 1

    do_heavy = heavy_budget[0] > 0

    if not memb and 2 <= tstar <= N - 2:
        # witness eps^{t*} = fA + gB
        combo = solve(d1_cols, dd.eps_pow[tstar])
        assert combo is not None, "membership at t* has no witness (bug)"
        f = combo & ((1 << n) - 1)
        g = combo >> n
        # S3: canonical violator z* = eps^{N-t*} (f, g)
        z1 = apply_cols(dd.epow_mats[N - tstar], f)
        z2 = apply_cols(dd.epow_mats[N - tstar], g)
        zst = z1 | (z2 << n)
        if apply_cols(d1_cols, zst) != 0:
            tally.violations.append(("S3-notcycle", A, B, f"t*={tstar}"))
        elif zst == 0:
            # eps^{N-t*}(f,g) = 0 would make the mechanism vacuous; the
            # proof still stands via s = eps^{N-t*} sigma, but flag it.
            tally.violations.append(("S3-zerocycle", A, B, f"t*={tstar}"))
        elif in_span(im2, apply_eps_c1(dd.eps_cols, n, zst)):
            tally.violations.append(("S3-VIOLATOR-SILENT", A, B,
                                     f"t*={tstar} (proof mechanism broken)"))
        else:
            tally.violator_fired += 1
        # S7: liveness — eps(f,g) is not a level-t* boundary
        efg = apply_eps_c1(dd.eps_cols, n,  f | (g << n))
        lev_bd = list(im2)
        for w in dd.W[tstar]:
            rref_add(lev_bd, w)
            rref_add(lev_bd, w << n)
        if in_span(lev_bd, efg):
            tally.violations.append(("S7-LIVENESS", A, B,
                                     f"t*={tstar} Ob=0 but eps not in I"))
        else:
            tally.ob_alive += 1

    if not memb and tstar >= N - 1:
        # S4: A12 regression on the top step (deck eps^{N/2})
        mu = dd.eps_pow[N // 2]
        if in_span(ideal, mu):
            tally.violations.append(("S4-mu-in-I", A, B, f"t*={tstar}"))
        else:
            mu_trivial = True
            for v in ker:
                w = 0
                low = v
                while low:
                    b = low & -low
                    c = b.bit_length() - 1
                    low ^= b
                    if c < n:
                        w ^= dd.epow_mats[N // 2][c]
                    else:
                        w ^= dd.epow_mats[N // 2][c - n] << n
                if not in_span(im2, w):
                    mu_trivial = False
                    break
            if mu_trivial:
                tally.violations.append(("S4-A12-REGRESSION", A, B,
                                         f"mu trivial but mu not in I"))
            else:
                tally.a12_regressions += 1

    # ---- heavy, subsampled checks ----
    if not do_heavy:
        return
    # pick a level u with a witness: t* if 1 <= t* <= N-1, else skip
    u = tstar if 1 <= tstar <= N - 1 else (N // 2 if memb else 0)
    if memb:
        u = 1  # eps itself is in I; use the sharpest level
    if not (1 <= u <= N - 1):
        return
    combo = solve(d1_cols, dd.eps_pow[u])
    if combo is None:
        return
    heavy_budget[0] -= 1
    f = combo & ((1 << n) - 1)
    g = combo >> n
    Wu = dd.W[u]
    W2 = []
    for w in Wu:
        rref_add(W2, w)
        rref_add(W2, w << n)

    # S5 / R3: level-u cycles = p(top cycles) + T*(f,g) + W^2
    red_cols = [reduce_span(Wu, c) for c in d1_cols]
    lev_ker = nullspace(red_cols, n)
    lhs = span_basis(lev_ker + list(W2))
    Mf = alg.elt_matrix(f)
    Mg = alg.elt_matrix(g)
    fg_mults = [Mf[c] | (Mg[c] << n) for c in range(n)]
    rhs = span_basis(ker + fg_mults + list(W2))
    union = span_basis(lhs + rhs)
    if not (len(lhs) == len(rhs) == len(union)):
        tally.violations.append(
            ("S5-R3", A, B,
             f"u={u} dims lhs={len(lhs)} rhs={len(rhs)} union={len(union)}"))
    else:
        tally.heavy_r3 += 1

    # S6: membership case — divided class dies at level u
    if memb:
        lev_bd = list(im2)
        for w in W2:
            rref_add(lev_bd, w)
        efg = apply_eps_c1(dd.eps_cols, n, f | (g << n))
        if not in_span(lev_bd, efg):
            tally.violations.append(("S6-Ob-alive-despite-memb", A, B,
                                     f"u={u}"))
        else:
            tally.heavy_s6 += 1

    # S8: Lemma 0 at level u
    lev_bd = list(im2)
    for w in W2:
        rref_add(lev_bd, w)
    dim_h1_direct = 2 * n - len(span_basis(red_cols)) - len(lev_bd)
    lev_ideal = list(ideal)
    for c in dd.epow_mats[u]:
        rref_add(lev_ideal, c)
    dim_h1_count = 2 * (n - len(lev_ideal))
    if dim_h1_direct != dim_h1_count:
        tally.violations.append(("S8-lemma0-level", A, B,
                                 f"u={u} {dim_h1_direct}!={dim_h1_count}"))
    else:
        tally.heavy_s8 += 1


# ---------- sweeps ----------

def sweep(name, alg, s_ij, N, pairs_iter, label, heavy_cap=400):
    dd = DeckData(alg, s_ij, N)
    tally = Tally()
    heavy_budget = [heavy_cap]
    t0 = time.time()
    for (A, B) in pairs_iter:
        check_pair(dd, A, B, tally, heavy_budget)
    dt = time.time() - t0
    geo = {k: v for k, v in sorted(tally.geography.items())}
    mixed = sum(v for (R, m), v in geo.items() if R != m)
    status = "OK" if not tally.violations else \
        f"{len(tally.violations)} VIOLATIONS"
    print(f"{name:16s} s={s_ij} N={N} pairs={tally.pairs:>8d} "
          f"R<->memb mismatches={mixed}  "
          f"S3 fired={tally.violator_fired:>6d}  S7 alive={tally.ob_alive:>6d} "
          f"S4={tally.a12_regressions:>5d}  "
          f"heavy(R3/S6/S8)={tally.heavy_r3}/{tally.heavy_s6}/{tally.heavy_s8} "
          f" {status}  [{label}, {dt:.1f}s]")
    if tally.tstar_hist:
        print(f"{'':16s} t* histogram (eps not in I): "
              f"{dict(sorted(tally.tstar_hist.items()))}")
    for v in tally.violations[:8]:
        print(f"    !! {v[0]}: A={v[1]:#x} B={v[2]:#x}  {v[3]}")
    return tally.violations


def hand_sanity():
    """The two hand-computed toy rows from the A13 planning session,
    T = F2[Z4xZ2] = F2[t,u]/(t^4,u^2), t = 1+x, u = 1+y, eps = t."""
    alg = BlockAlgebra(4, 2, 1)
    dd = DeckData(alg, (1, 0), 4)
    one = 1 << alg.coord(0, alg.pidx(0, 0))
    y = 1 << alg.coord(0, alg.pidx(0, 1))
    uu = one | y                       # u = 1 + y
    t2 = one | (1 << alg.coord(0, alg.pidx(2, 0)))   # t^2 = 1 + x^2
    assert dd.eps_pow[2] == t2, "eps^2 != 1+x^2"
    # row 1: A = u, B = t^2 : t* = 2, eps not in I, (R) fails
    tally = Tally()
    check_pair(dd, uu, t2, tally, [10])
    assert tally.geography.get((False, False), 0) == 1, "toy row 1: expected (R) fail + eps not in I"
    assert tally.violator_fired == 1 and tally.ob_alive == 1
    assert not tally.violations, tally.violations
    # row 2: A = u, B = t*u : t* = 4 (residual regime), (R) fails via S4
    tu = apply_cols(dd.eps_cols, uu)
    tally = Tally()
    check_pair(dd, uu, tu, tally, [10])
    assert tally.geography.get((False, False), 0) == 1
    assert tally.a12_regressions == 1
    assert not tally.violations, tally.violations
    print("hand-computed toy rows reproduced (A=u,B=t^2 and A=u,B=tu)")


def main():
    random.seed(20260702)
    all_violations = []

    hand_sanity()
    print()

    # exhaustive, N = 4 and N = 8
    exhaustive = [
        ("F2[Z4]",    BlockAlgebra(4, 1, 1),  (1, 0), 4),
        ("F2[Z8]",    BlockAlgebra(8, 1, 1),  (2, 0), 4),
        ("F2[Z8]",    BlockAlgebra(8, 1, 1),  (1, 0), 8),
        ("F4[Z4]",    BlockAlgebra(4, 1, 2),  (1, 0), 4),
        ("F2[Z4xZ2]", BlockAlgebra(4, 2, 1),  (1, 0), 4),
        ("F2[Z4xZ2]", BlockAlgebra(4, 2, 1),  (1, 1), 4),
    ]
    for name, alg, s_ij, N in exhaustive:
        assert elt_order(alg.pa, alg.pb, *s_ij) == N
        n_elts = 1 << alg.n
        pairs = itertools.product(range(n_elts), repeat=2)
        all_violations += sweep(name, alg, s_ij, N, pairs, "exhaustive")

    # sampled: uniform + targeted (B = eps^2 + c*A forces eps^2 in I)
    SAMPLE = 20000
    sampled = [
        ("F2[Z8xZ2]", BlockAlgebra(8, 2, 1), (1, 0), 8),
        ("F2[Z8xZ2]", BlockAlgebra(8, 2, 1), (2, 1), 4),
        ("F2[Z4xZ4]", BlockAlgebra(4, 4, 1), (1, 0), 4),
        ("F2[Z4xZ4]", BlockAlgebra(4, 4, 1), (1, 1), 4),
        ("F4[Z4xZ2]", BlockAlgebra(4, 2, 2), (1, 0), 4),
    ]
    for name, alg, s_ij, N in sampled:
        assert elt_order(alg.pa, alg.pb, *s_ij) == N
        nbits = alg.n
        dd_tmp = DeckData(alg, s_ij, N)
        eps2 = dd_tmp.eps_pow[2]

        def uniform():
            for _ in range(SAMPLE):
                yield random.getrandbits(nbits), random.getrandbits(nbits)

        def targeted():
            for _ in range(SAMPLE):
                A = random.getrandbits(nbits)
                c = random.getrandbits(nbits)
                B = eps2 ^ apply_cols(alg.elt_matrix(A), c)
                yield A, B

        all_violations += sweep(name, alg, s_ij, N, uniform(),
                                f"uniform {SAMPLE}")
        all_violations += sweep(name, alg, s_ij, N, targeted(),
                                f"targeted eps^2-in-I {SAMPLE}")

    print()
    if all_violations:
        s1 = [v for v in all_violations if v[0].startswith("S1")]
        print(f"FAIL: {len(all_violations)} violations total, "
              f"{len(s1)} S1 counterexamples to Theorem A13.")
        sys.exit(1)
    print("ALL PASS: (R) <=> eps in (A,B) on every pair swept; the "
          "canonical violator fires and the divided class is eps-alive "
          "in every 2 <= t* <= N-2 pair; A12 top-step regression clean; "
          "R3/S6/S8 structural checks clean on the heavy subsample.")


if __name__ == "__main__":
    main()
