"""A13 C3: the gross x-tower is certified uniformly in r (P0/T1), plus a
cover-level r=2 spot sweep.

Part 1 (the ladder): for L in {6, 12, 24, 48} (levels j = 0..3 of the
gross x-tower Z_L x Z_6, same polynomials A = x^3+y+y^2, B = y^3+x+x^2):

  W1: the witness identity (1+x^2) * B^2 = 1 + x^6 holds in F2[Z_L x Z_6]
      (it only uses y^6 = 1, so it is level-free)
  W2: 1 + x^6 lies in the principal ideal (B) — hence in (A,B) — at every
      level (R0-shaped membership)
  W3: k(level) = 12 at every level, via Lemma 0 (k = 2 dim T/(A,B)) and
      via the direct H1 dimension, with rank d1 = rank d2 (Frobenius)
  W4: the full deck acts trivially on H1 at every level:
      (1+x^6) * Z1 <= B1 (deck-triviality, checked directly, not via K2)
  W5: T1 k-profile inside each level ring: k_j = 2 dim T/((A,B) +
      (1+x^{6*2^j})) equals 12 for every sub-level j (monotone, constant)

Part 2 (cover-level r=2 spot sweep): Z_12 x Z_3 as a Z_4-tower over
Z_3 x Z_3 (deck x^3, eps = 1+x^3, N = 4). Random weight-3 cover pairs
run through the full A13 battery of a13_deck_tower_block_sweep.check_pair
(S1 endpoint, S3 canonical violator, S7 liveness, S4 A12 regression,
heavy R3/S8 subsample) — the same checks, now on genuine BB cover pairs
rather than abstract block pairs.

Run: python3 scripts/a13_gross_ladder.py   (from experiments/bb_lab)
"""

import os
import random
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from a12_bockstein_block_sweep import BlockAlgebra, nullspace, rref_add  # noqa: E402
from a13_deck_tower_block_sweep import (  # noqa: E402
    DeckData, Tally, apply_cols, apply_eps_c1, check_pair, in_span,
    span_basis)


def gross_level(L):
    """Run W1-W5 for the level ring F2[Z_L x Z_6]; return (k, report)."""
    alg = BlockAlgebra(L, 6, 1)
    n = alg.n

    def mono(i, j):
        return 1 << alg.coord(0, alg.pidx(i, j))

    A = mono(3, 0) ^ mono(0, 1) ^ mono(0, 2)
    B = mono(0, 3) ^ mono(1, 0) ^ mono(2, 0)
    MA = alg.elt_matrix(A)
    MB = alg.elt_matrix(B)
    d1_cols = MA + MB

    ideal = span_basis(d1_cols)
    rank1 = len(ideal)
    im2 = span_basis([MB[h] | (MA[h] << n) for h in range(n)])
    assert len(im2) == rank1, f"L={L}: rank d2 != rank d1 (Lemma 0)"

    k_lemma0 = 2 * (n - rank1)
    ker = nullspace(d1_cols, n)
    k_direct = len(ker) - rank1  # dim Z1 - dim B1 = (2n - rank1) - rank1
    assert len(ker) == 2 * n - rank1
    assert k_direct == k_lemma0 == 12, \
        f"L={L}: k = {k_direct}/{k_lemma0}, expected 12"

    eps = mono(0, 0) ^ (mono(6, 0) if 6 % L or L > 6 else 0)
    if L == 6:
        eps = 0  # x^6 = 1 at the base: the deck is trivial there
    report = [f"k={k_direct}"]

    if L > 6:
        # W1: (1+x^2) * B^2 = 1 + x^6, level-free witness
        B2 = apply_cols(MB, B)
        lhs = apply_cols(alg.elt_matrix(mono(0, 0) ^ mono(2, 0)), B2)
        assert lhs == eps, f"L={L}: witness identity fails"
        # W2: R0-shaped membership 1+x^6 in (B), hence in (A,B)
        assert in_span(span_basis(MB), eps), f"L={L}: eps not in (B)"
        assert in_span(ideal, eps), f"L={L}: eps not in (A,B)"
        # W4: full-deck triviality on H1, checked directly
        eps_cols = alg.elt_matrix(eps)
        for z in ker:
            assert in_span(im2, apply_eps_c1(eps_cols, n, z)), \
                f"L={L}: deck acts nontrivially on H1"
        report.append("witness+membership+deck-trivial OK")

    # W5: T1 k-profile inside this level ring
    m = (L // 6).bit_length() - 1  # L = 6 * 2^m
    kprof = []
    for j in range(m + 1):
        e = (6 * (1 << j)) % L
        lev = list(ideal)
        if e:
            for c in alg.elt_matrix(mono(0, 0) ^ mono(e, 0)):
                rref_add(lev, c)
        kprof.append(2 * (n - len(lev)))
    assert kprof == [12] * (m + 1), f"L={L}: k-profile {kprof}"
    report.append(f"k-profile {kprof}")
    return k_direct, "; ".join(report)


def cover_r2_sweep(samples=15000, heavy_cap=150):
    """Weight-3 cover pairs on Z12 x Z3 (deck x^3 of order 4)."""
    alg = BlockAlgebra(12, 3, 1)
    n = alg.n
    dd = DeckData(alg, (3, 0), 4)
    tally = Tally()
    heavy_budget = [heavy_cap]
    coords = [1 << c for c in range(n)]
    t0 = time.time()
    for _ in range(samples):
        A = 0
        for c in random.sample(coords, 3):
            A ^= c
        B = 0
        for c in random.sample(coords, 3):
            B ^= c
        check_pair(dd, A, B, tally, heavy_budget)
    dt = time.time() - t0
    geo = dict(sorted(tally.geography.items()))
    mixed = sum(v for (R, mb), v in geo.items() if R != mb)
    print(f"Z12xZ3 weight-3 r=2 sweep: pairs={tally.pairs} "
          f"geography={geo} R<->memb mismatches={mixed}")
    print(f"  t* histogram (eps not in I): "
          f"{dict(sorted(tally.tstar_hist.items()))}")
    print(f"  S3 violator fired={tally.violator_fired} "
          f"S7 divided-class alive={tally.ob_alive} "
          f"S4 A12-regressions={tally.a12_regressions} "
          f"heavy R3/S6/S8={tally.heavy_r3}/{tally.heavy_s6}/{tally.heavy_s8}"
          f"  [{dt:.1f}s]")
    return tally.violations


def main():
    random.seed(20260702)
    print("Part 1: gross x-tower ladder, levels Z_L x Z_6")
    for L in (6, 12, 24, 48):
        t0 = time.time()
        _, report = gross_level(L)
        print(f"  L={L:>2d} ([[{2 * 6 * L},12,.]]): {report} "
              f"[{time.time() - t0:.1f}s]")
    print("Part 1 ALL PASS: k = 12 and full deck-triviality certified at "
          "every level by the single level-free witness (1+x^2)B^2 = 1+x^6.")
    print()
    print("Part 2: cover-level r=2 battery on Z12 x Z3")
    violations = cover_r2_sweep()
    if violations:
        for v in violations[:8]:
            print(f"    !! {v[0]}: A={v[1]:#x} B={v[2]:#x}  {v[3]}")
        print(f"FAIL: {len(violations)} violations")
        sys.exit(1)
    print("Part 2 ALL PASS.")


if __name__ == "__main__":
    main()
