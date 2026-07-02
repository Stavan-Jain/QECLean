"""A12 Phase B4: exhaustive local-block sweep for the Bockstein conjecture.

The CRT-block reduction says H1 of a free-Z2 BB cover decomposes over blocks
T = S[P] (S = F_{2^d} from the odd characters, P = 2-part of the cover
group, always containing the deck element s of order 2, eps = 1+s). Since a
BB group has two cyclic factors, realizable P are Z_{2^a} x Z_{2^b}.

Per block-pair (A, B) in T^2 this script computes
    E = dim_F2 eps*H1( T ->(B,A) T^2 ->(A,B) T )
    g = dim_F2 ((eps) + (A,B)) / (A,B)
and checks
    THEOREM-INEQ:  E >= 2g          (transfer-LES bookkeeping)
    THEOREM-T1:    g = 0 => E = 0   (Koszul homology killed by (A,B))
    CONJ-EQ:       E == 2g          (<=> Bockstein delta^2 = 0 on the block)

Any pair with E > 2g is a counterexample to the quantitative conjecture
(and is dumped); any E < 2g or (g=0, E>0) would falsify the *theorems*
(i.e. a bug in the derivation or the code).

Coverage: exhaustive over all pairs for F2[P], |P| <= 8, and F4[P],
|P| <= 4; random-sampled for F2[P] with |P| = 16 and F4[P] with |P| = 8.
All order-2 deck choices s in P are swept.

Run: python3 scripts/a12_bockstein_block_sweep.py   (from experiments/bb_lab)
"""

import itertools
import random


# ---------- F2 bitmask linear algebra ----------

def rref_add(basis, v):
    """Reduce v against basis (list of pivot rows); append if independent."""
    for b in basis:
        v = min(v, v ^ b)
    if v:
        basis.append(v)
        basis.sort(reverse=True)
        return True
    return False


def rank_of(vectors):
    basis = []
    for v in vectors:
        rref_add(basis, v)
    return len(basis)


def nullspace(cols, _nrows):
    """Kernel of the linear map with the given columns (ints over rows).

    Returns kernel basis as bitmasks over column indices."""
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


# ---------- block algebras T = S[P], S in {F2, F4}, P = Z_{2^a} x Z_{2^b} --

class BlockAlgebra:
    """T = S[P] with F2-basis indexed by (omega^e, p), e < d, p in P.

    Elements are int bitmasks over n = d*|P| coordinates.
    coordinate index = e * |P| + p_index.
    """

    def __init__(self, pa, pb, d):
        self.pa, self.pb, self.d = pa, pb, d
        self.np = pa * pb
        self.n = d * self.np
        # F4 multiplication table on exponent-of-omega basis {1, omega}:
        # mult by omega:  1 -> omega, omega -> 1 + omega
        # (d = 1: trivial)

    def pidx(self, i, j):
        return (i % self.pa) * self.pb + (j % self.pb)

    def coord(self, e, p):
        return e * self.np + p

    def mono_matrix(self, e, i, j):
        """Columns of multiplication by omega^e * x^i y^j (e < 2 if d=2)."""
        n = self.n
        cols = [0] * n
        for p_i in range(self.pa):
            for p_j in range(self.pb):
                src_p = self.pidx(p_i, p_j)
                dst_p = self.pidx(p_i + i, p_j + j)
                for se in range(self.d):
                    src = self.coord(se, src_p)
                    te = se + e
                    if self.d == 1:
                        cols[src] |= 1 << self.coord(0, dst_p)
                    else:
                        # F4: omega^te on basis {1, omega}
                        te %= 3
                        if te == 0:
                            cols[src] |= 1 << self.coord(0, dst_p)
                        elif te == 1:
                            cols[src] |= 1 << self.coord(1, dst_p)
                        else:  # omega^2 = 1 + omega
                            cols[src] |= 1 << self.coord(0, dst_p)
                            cols[src] |= 1 << self.coord(1, dst_p)
        return cols

    def elt_matrix(self, elt):
        """elt = int bitmask over coords -> multiplication matrix columns."""
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

    def order2_elements(self):
        """All order-2 group elements s of P (as (i, j) exponent pairs)."""
        out = []
        for i in range(self.pa):
            for j in range(self.pb):
                if (i, j) == (0, 0):
                    continue
                if (2 * i) % self.pa == 0 and (2 * j) % self.pb == 0:
                    out.append((i, j))
        return out


def check_pair(alg, MA, MB, eps_cols, eps_im_basis, d1_ranks_cache=None):
    """Return (E, g) for the pair with multiplication matrices MA, MB."""
    n = alg.n
    # d1 : T^2 -> T, columns [MA | MB]
    d1_cols = MA + MB
    ker = nullspace(d1_cols, n)  # bitmasks over 2n C1-coords
    # d2 : T -> T^2, column for basis h: (MB[h], MA[h]) stacked
    im2 = []
    for h in range(n):
        rref_add(im2, MB[h] | (MA[h] << n))
    r2 = len(im2)
    # eps action on C1 = T^2 (blockwise)
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
    # g = dim ((eps)+(A,B))/(A,B): ideal (A,B) = column space of [MA|MB]
    ideal = []
    for c in d1_cols:
        rref_add(ideal, c)
    rAB = len(ideal)
    for c in eps_cols:
        rref_add(ideal, c)
    g = len(ideal) - rAB
    return E, g


def sweep_block(name, alg, s_ij, pairs_iter, n_pairs_label):
    eps = 0
    # eps = 1 + s as an element: coords (e=0, p=0) and (e=0, p=s)
    eps |= 1 << alg.coord(0, alg.pidx(0, 0))
    eps |= 1 << alg.coord(0, alg.pidx(*s_ij))
    eps_cols = alg.elt_matrix(eps)

    n_checked = 0
    n_gap_pos = 0
    violations = []
    for (A, B) in pairs_iter:
        MA = alg.elt_matrix(A)
        MB = alg.elt_matrix(B)
        E, g = check_pair(alg, MA, MB, eps_cols, None)
        n_checked += 1
        if g > 0:
            n_gap_pos += 1
        if E < 2 * g or (g == 0 and E > 0):
            violations.append(("THEOREM", A, B, E, g))
        elif E != 2 * g:
            violations.append(("CONJ-EQ", A, B, E, g))
    status = "OK" if not violations else f"{len(violations)} VIOLATIONS"
    print(f"{name:34s} s={s_ij} pairs={n_checked:>8d} "
          f"(g>0 on {n_gap_pos:>7d})  {status}  [{n_pairs_label}]")
    for kind, A, B, E, g in violations[:5]:
        print(f"    !! {kind}: A={A:#x} B={B:#x} E={E} g={g}")
    return violations


def main():
    random.seed(20260702)
    all_violations = []

    # exhaustive: F2[P], |P| <= 8
    for (pa, pb) in [(2, 1), (4, 1), (2, 2), (8, 1), (4, 2)]:
        alg = BlockAlgebra(pa, pb, 1)
        n_elts = 1 << alg.n
        for s_ij in alg.order2_elements():
            pairs = itertools.product(range(n_elts), repeat=2)
            all_violations += sweep_block(
                f"F2[Z{pa}xZ{pb}]" if pb > 1 else f"F2[Z{pa}]",
                alg, s_ij, pairs, "exhaustive")

    # exhaustive: F4[P], |P| <= 4
    for (pa, pb) in [(2, 1), (4, 1), (2, 2)]:
        alg = BlockAlgebra(pa, pb, 2)
        n_elts = 1 << alg.n
        for s_ij in alg.order2_elements():
            pairs = itertools.product(range(n_elts), repeat=2)
            all_violations += sweep_block(
                f"F4[Z{pa}xZ{pb}]" if pb > 1 else f"F4[Z{pa}]",
                alg, s_ij, pairs, "exhaustive")

    # sampled: F2[P], |P| = 16 and F4[P], |P| = 8
    SAMPLE = 30000
    for (pa, pb, d) in [(16, 1, 1), (8, 2, 1), (4, 4, 1), (8, 1, 2),
                        (4, 2, 2)]:
        alg = BlockAlgebra(pa, pb, d)
        n_elts_bits = alg.n
        for s_ij in alg.order2_elements():
            pairs = ((random.getrandbits(n_elts_bits),
                      random.getrandbits(n_elts_bits))
                     for _ in range(SAMPLE))
            base = f"F{2 ** d}[Z{pa}" + (f"xZ{pb}]" if pb > 1 else "]")
            all_violations += sweep_block(
                base, alg, s_ij, pairs, f"sampled {SAMPLE}")

    print()
    if all_violations:
        theorem_v = [v for v in all_violations if v[0] == "THEOREM"]
        conj_v = [v for v in all_violations if v[0] == "CONJ-EQ"]
        print(f"TOTAL: {len(theorem_v)} theorem violations (BUG if any), "
              f"{len(conj_v)} Bockstein counterexamples")
    else:
        print("ALL BLOCKS CLEAN: E = 2g everywhere "
              "(Bockstein delta^2 = 0 conjecture holds on every block "
              "swept; theorems hold everywhere).")


if __name__ == "__main__":
    main()
