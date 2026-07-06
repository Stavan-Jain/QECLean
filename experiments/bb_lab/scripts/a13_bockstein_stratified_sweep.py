"""A13 session-0: stratified sweep + tower-lift validation for OQ2 (Bockstein).

Extends `a12_bockstein_block_sweep.py` (kept untouched as the A12 record) in
four directions, per `notes/A13_bockstein_equality_plan.md`:

1. **F8 coefficients** (`d = 3`) — the "untouched S = F8 residue fields"
   stratum of OQ2.
2. **Biased sampling** toward the informative stratum: uniform pairs on a
   local algebra are units half the time and land at g = 0 almost always;
   strategies `m` (both in the maximal ideal), `prod2`/`prod3` (products of
   maximal-ideal elements) push into deep ideals where g > 0 lives.  Each
   block reports the g>0 count *and* the LIVE count (g > 0 with both A, B
   nonzero mod eps — the only stratum where delta_2 and delta_1 can both be
   nonzero, i.e. where the conjecture has actual content).
3. **Element-form spot check** (every ELEM_EVERY-th pair): for a basis of
   Z = {z : Az, Bz in eps*T}, solve eps*a = Az, eps*b = Bz and assert
   W = A*b + B*a  in  eps*(A,B)  — the sharpest OQ2 form, checked directly
   and independently of the E = 2g bookkeeping route.
4. **Tower-lift pillar check** per (block, deck): build the Z/4-lift
   T^ = S[P^] (double the deck coordinate, s^ = same exponents, order 4,
   eps^ = 1 + s^) and assert  rank(eps^) = 3n/4  and  rank(eps^3) = n/4,
   which together with eps^4 = 0 give  Ann(eps^) = eps^3 T^  — the only
   nontrivial input of the A13 candidate proof (freeness over F2[Z/4]).

Per pair the main sweep computes (as in A12)
    E = dim_F2 eps*H1( T ->(B,A) T^2 ->(A,B) T )
    g = dim_F2 ((eps) + (A,B)) / (A,B)        [so k~ - k = 2g]
and checks THEOREM-INEQ (E >= 2g), THEOREM-T1 (g = 0 => E = 0), and
CONJ-EQ (E == 2g  <=>  delta_1 delta_2 = 0 on the block).

Also re-runs the A12 global regression rows CE1/CE2 on F2[Z6xZ3] and adds
twisted decks (s = x^3 y^3 on Z6xZ6) that the axis-pure A12 sweeps never
exercised.

Run:  python3 scripts/a13_bockstein_stratified_sweep.py           (quick)
      python3 scripts/a13_bockstein_stratified_sweep.py --full    (W1 sizes)
"""

import itertools
import random
import sys


# ---------- F2 bitmask linear algebra (as in A12, plus a solver) ----------

def rref_add(basis, v):
    """Reduce v against basis (list of pivot rows); append if independent."""
    for b in basis:
        v = min(v, v ^ b)
    if v:
        basis.append(v)
        basis.sort(reverse=True)
        return True
    return False


def reduce_vec(basis, v):
    for b in basis:
        v = min(v, v ^ b)
    return v


def rank_of(vectors):
    basis = []
    for v in vectors:
        rref_add(basis, v)
    return len(basis)


def nullspace(cols, _nrows):
    """Kernel of the linear map with the given columns (ints over rows)."""
    piv = []
    ker = []
    for j, c in enumerate(cols):
        comb = 1 << j
        for pv, pc in piv:
            low = pv & -pv
            if c & low:
                c ^= pv
                comb ^= pc
        if c:
            piv.append((c, comb))
        else:
            ker.append(comb)
    return ker


def make_solver(cols):
    """Return solve(t) -> x with sum_{c in bits(x)} cols[c] = t, or None."""
    piv = []
    for j, c in enumerate(cols):
        comb = 1 << j
        for pv, pc in piv:
            low = pv & -pv
            if c & low:
                c ^= pv
                comb ^= pc
        if c:
            piv.append((c, comb))

    def solve(t):
        x = 0
        for pv, pc in piv:
            low = pv & -pv
            if t & low:
                t ^= pv
                x ^= pc
        return x if t == 0 else None

    return solve


def apply_cols(cols, v):
    w = 0
    while v:
        b = v & -v
        v ^= b
        w ^= cols[b.bit_length() - 1]
    return w


# ---------- block algebras T = S[P], S = F_{2^d}, P = Z_pa x Z_pb ----------

# POW[d][t] = bitmask of gen^t over the field basis {1, gen, ..., gen^{d-1}}
# F4:  w^2 = 1 + w.       F8:  h^3 = 1 + h  (so h has multiplicative order 7).
POW = {
    1: [0b1],
    2: [0b01, 0b10, 0b11],
    3: [0b001, 0b010, 0b100, 0b011, 0b110, 0b111, 0b101],
}


class BlockAlgebra:
    """T = S[P]; elements are int bitmasks over n = d*|P| coordinates.

    coordinate index = e * |P| + p_index   (e = field-basis exponent < d).
    Works for any cyclic orders (pa, pb), not just 2-powers — so the same
    class drives local blocks AND full group algebras (global regressions).
    """

    def __init__(self, pa, pb, d):
        self.pa, self.pb, self.d = pa, pb, d
        self.np = pa * pb
        self.n = d * self.np
        self.q = (1 << d) - 1  # multiplicative order of the field generator

    def pidx(self, i, j):
        return (i % self.pa) * self.pb + (j % self.pb)

    def coord(self, e, p):
        return e * self.np + p

    def mono_matrix(self, e, i, j):
        """Columns of multiplication by gen^e * x^i y^j."""
        cols = [0] * self.n
        pow_d = POW[self.d]
        for p_i in range(self.pa):
            for p_j in range(self.pb):
                src_p = self.pidx(p_i, p_j)
                dst_p = self.pidx(p_i + i, p_j + j)
                for se in range(self.d):
                    src = self.coord(se, src_p)
                    fld = pow_d[(se + e) % self.q] if self.q > 1 else 1
                    ff = fld
                    while ff:
                        fb = ff & -ff
                        ff ^= fb
                        cols[src] |= 1 << self.coord(
                            fb.bit_length() - 1, dst_p)
        return cols

    def elt_matrix(self, elt):
        cols = [0] * self.n
        for c in range(self.n):
            if not (elt >> c) & 1:
                continue
            e, p = divmod(c, self.np)
            i, j = divmod(p, self.pb)
            mono = self.mono_matrix(e, i, j)
            for src in range(self.n):
                cols[src] ^= mono[src]
        return cols

    def mul(self, u, v):
        return apply_cols(self.elt_matrix(u), v)

    def monomial(self, e, i, j):
        return 1 << self.coord(e, self.pidx(i, j))

    def order2_elements(self):
        out = []
        for i in range(self.pa):
            for j in range(self.pb):
                if (i, j) == (0, 0):
                    continue
                if (2 * i) % self.pa == 0 and (2 * j) % self.pb == 0:
                    out.append((i, j))
        return out

    def rand_elt(self):
        return random.getrandbits(self.n)

    def rand_maximal(self):
        """Random element of the maximal ideal of a LOCAL S[P] (P a 2-group):
        augmentation (sum over P per field coordinate) = 0."""
        v = random.getrandbits(self.n)
        for e in range(self.d):
            sl = (v >> (e * self.np)) & ((1 << self.np) - 1)
            if bin(sl).count("1") % 2:
                v ^= 1 << self.coord(e, random.randrange(self.np))
        return v


# ---------- per-pair checks ----------

def check_pair(alg, MA, MB, eps_cols):
    """Return (E, g) as in the A12 sweep."""
    n = alg.n
    d1_cols = MA + MB
    ker = nullspace(d1_cols, n)
    im2 = []
    for h in range(n):
        rref_add(im2, MB[h] | (MA[h] << n))
    E_basis = list(im2)
    E = 0
    for v in ker:
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
        if rref_add(E_basis, w):
            E += 1
    ideal = []
    for c in d1_cols:
        rref_add(ideal, c)
    rAB = len(ideal)
    for c in eps_cols:
        rref_add(ideal, c)
    g = len(ideal) - rAB
    return E, g


def element_form_check(alg, MA, MB, eps_cols):
    """Directly check OQ2's element form on this pair.

    For every z in a basis of Z = {z : Az, Bz in eps*T}: solve eps*a = Az,
    eps*b = Bz and test  W = A*b + B*a  in  eps*(A,B).
    Returns None if clean, else a witness tuple.
    """
    n = alg.n
    eps_im = []
    for c in eps_cols:
        rref_add(eps_im, c)
    # Z = kernel of z -> (Az mod eps, Bz mod eps)
    zcols = []
    for c in range(n):
        ra = reduce_vec(eps_im, MA[c])
        rb = reduce_vec(eps_im, MB[c])
        zcols.append(ra | (rb << n))
    zbasis = nullspace(zcols, 2 * n)
    if not zbasis:
        return None
    solve_eps = make_solver(eps_cols)
    # eps*(A,B) = span{ eps*A*e_p, eps*B*e_p }
    epsAB = []
    for c in range(n):
        rref_add(epsAB, apply_cols(eps_cols, MA[c]))
        rref_add(epsAB, apply_cols(eps_cols, MB[c]))
    for z in zbasis:
        az = apply_cols(MA, z)
        bz = apply_cols(MB, z)
        a = solve_eps(az)
        b = solve_eps(bz)
        if a is None or b is None:  # cannot happen if Z was computed right
            return ("SOLVE-FAIL", z)
        W = apply_cols(MA, b) ^ apply_cols(MB, a)
        if reduce_vec(epsAB, W):
            return ("ELEM-FORM", z, W)
    return None


def tower_lift_check(pa, pb, d, s_ij):
    """Build the Z/4-lift of (S[Z_pa x Z_pb], s) and verify Ann(eps^) = eps^3.

    Doubles the coordinate where s has a nonzero exponent; s^ keeps the same
    exponents and then has order 4, eps^ = 1 + s^.  Checks rank(eps^) = 3n/4,
    rank(eps^3) = n/4 (with eps^4 = 0 these force Ann(eps^) = eps^3 T^)."""
    i, j = s_ij
    if i != 0:
        lift = BlockAlgebra(2 * pa, pb, d)
    else:
        lift = BlockAlgebra(pa, 2 * pb, d)
    # s^ must have order 4 in the lifted group
    assert (2 * i) % lift.pa != 0 or (2 * j) % lift.pb != 0
    assert (4 * i) % lift.pa == 0 and (4 * j) % lift.pb == 0
    eps_hat = lift.monomial(0, 0, 0) ^ lift.monomial(0, i, j)
    M = lift.elt_matrix(eps_hat)
    e2 = apply_cols(M, eps_hat)
    e3 = apply_cols(M, e2)
    assert apply_cols(M, e3) == 0, "eps^4 != 0 ?!"
    M3 = lift.elt_matrix(e3)
    r1, r3 = rank_of(M), rank_of(M3)
    ok = (r1 == 3 * lift.n // 4) and (r3 == lift.n // 4)
    return ok, r1, r3, lift.n


# ---------- sweep driver ----------

ELEM_EVERY = 37  # element-form spot-check cadence


def sweep_block(name, alg, s_ij, pairs_iter, label, do_elem=True):
    eps = alg.monomial(0, 0, 0) ^ alg.monomial(0, *s_ij)
    eps_cols = alg.elt_matrix(eps)
    eps_im = []
    for c in eps_cols:
        rref_add(eps_im, c)

    n_checked = n_gap = n_live = n_elem = 0
    violations = []
    for (A, B) in pairs_iter:
        MA = alg.elt_matrix(A)
        MB = alg.elt_matrix(B)
        E, g = check_pair(alg, MA, MB, eps_cols)
        n_checked += 1
        if g > 0:
            n_gap += 1
            live = (reduce_vec(eps_im, A) != 0
                    and reduce_vec(eps_im, B) != 0)
            if live:
                n_live += 1
        if E < 2 * g or (g == 0 and E > 0):
            violations.append(("THEOREM", A, B, E, g))
        elif E != 2 * g:
            violations.append(("CONJ-EQ", A, B, E, g))
        if do_elem and (n_checked % ELEM_EVERY == 0 or violations):
            n_elem += 1
            w = element_form_check(alg, MA, MB, eps_cols)
            if w is not None:
                violations.append((w[0], A, B, E, g))
    status = "OK" if not violations else f"{len(violations)} VIOLATIONS"
    print(f"{name:22s} s={s_ij} pairs={n_checked:>7d} g>0:{n_gap:>6d} "
          f"live:{n_live:>6d} elem:{n_elem:>5d}  {status}  [{label}]",
          flush=True)
    for kind, A, B, E, g in violations[:5]:
        print(f"    !! {kind}: A={A:#x} B={B:#x} E={E} g={g}")
    return violations


def strategy_pairs(alg, strategy, count):
    for _ in range(count):
        if strategy == "unif":
            yield alg.rand_elt(), alg.rand_elt()
        elif strategy == "m":
            yield alg.rand_maximal(), alg.rand_maximal()
        elif strategy == "prod2":
            yield (alg.mul(alg.rand_maximal(), alg.rand_maximal()),
                   alg.mul(alg.rand_maximal(), alg.rand_maximal()))
        elif strategy == "prod3":
            a = alg.mul(alg.mul(alg.rand_maximal(), alg.rand_maximal()),
                        alg.rand_maximal())
            b = alg.mul(alg.mul(alg.rand_maximal(), alg.rand_maximal()),
                        alg.rand_maximal())
            yield a, b
        else:
            raise ValueError(strategy)


def run_strategies(name, alg, per_strategy, strategies=("unif", "m",
                                                        "prod2", "prod3")):
    out = []
    for s_ij in alg.order2_elements():
        ok, r1, r3, nn = tower_lift_check(alg.pa, alg.pb, alg.d, s_ij)
        if not ok:
            print(f"    !! TOWER-LIFT rank failure on {name} s={s_ij}: "
                  f"rank(eps^)={r1} (want {3 * nn // 4}), "
                  f"rank(eps^3)={r3} (want {nn // 4})")
            out.append(("TOWER", name, s_ij, r1, r3))
        for st in strategies:
            out += sweep_block(f"{name}:{st}", alg, s_ij,
                               strategy_pairs(alg, st, per_strategy),
                               f"sampled {per_strategy}")
    return out


def poly(alg, *monos):
    v = 0
    for (i, j) in monos:
        v ^= alg.monomial(0, i, j)
    return v


def main():
    full = "--full" in sys.argv
    random.seed(20260702 + 13)
    V = []

    # --- 1. F2[P], |P| = 16 — the OQ2 "cheapest falsification" stratum ---
    per = 12000 if full else 3000
    for (pa, pb) in [(16, 1), (8, 2), (4, 4)]:
        alg = BlockAlgebra(pa, pb, 1)
        V += run_strategies(f"F2[Z{pa}xZ{pb}]" if pb > 1 else f"F2[Z{pa}]",
                            alg, per)

    # --- 2. F8[P] — untouched residue fields ---
    alg = BlockAlgebra(2, 1, 3)
    for s_ij in alg.order2_elements():
        ok, r1, r3, nn = tower_lift_check(2, 1, 3, s_ij)
        assert ok, "tower lift fails on F8[Z2]"
        n_elts = 1 << alg.n
        V += sweep_block("F8[Z2]", alg, s_ij,
                         itertools.product(range(n_elts), repeat=2),
                         "exhaustive")
    per8 = 8000 if full else 2000
    for (pa, pb) in [(4, 1), (2, 2)]:
        V += run_strategies(f"F8[Z{pa}xZ{pb}]" if pb > 1 else f"F8[Z{pa}]",
                            BlockAlgebra(pa, pb, 3), per8)

    # --- 3. F4[P], |P| = 8 — previously random-only ---
    per4 = 8000 if full else 2000
    for (pa, pb) in [(8, 1), (4, 2)]:
        V += run_strategies(f"F4[Z{pa}xZ{pb}]" if pb > 1 else f"F4[Z{pa}]",
                            BlockAlgebra(pa, pb, 2), per4)

    # --- 4. global regressions: A12's CE rows on F2[Z6xZ3], deck s = x^3 ---
    alg = BlockAlgebra(6, 3, 1)
    ce1_A = poly(alg, (0, 0), (0, 1), (0, 2))
    ce1_B = poly(alg, (2, 0), (2, 1), (2, 2))
    ce2_B = poly(alg, (0, 0), (2, 0), (4, 0))
    V += sweep_block("F2[Z6xZ3] CE-rows", alg, (3, 0),
                     iter([(ce1_A, ce1_B), (ce1_A, ce2_B)]), "regression")
    V += run_strategies("F2[Z6xZ3]", alg, 1500 if not full else 6000)

    # --- 5. global twisted decks: Z6xZ6 with s in {x^3, y^3, x^3 y^3} ---
    V += run_strategies("F2[Z6xZ6]", BlockAlgebra(6, 6, 1),
                        800 if not full else 4000)

    print()
    th = [v for v in V if v[0] in ("THEOREM", "SOLVE-FAIL", "TOWER")]
    ce = [v for v in V if v[0] in ("CONJ-EQ", "ELEM-FORM")]
    if th:
        print(f"BUG-CLASS FAILURES: {len(th)} (derivation or code)")
    if ce:
        print(f"BOCKSTEIN COUNTEREXAMPLES: {len(ce)}")
    if not V:
        print("ALL CLEAN: E = 2g everywhere, element form holds on every "
              "spot-checked pair, tower-lift ranks correct on every block.")


if __name__ == "__main__":
    main()
