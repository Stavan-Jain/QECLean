"""A13 W1: EXHAUSTIVE Bockstein-equality check on |P| = 16 / F4 / F8 blocks,
via unit-orbit reduction.

Exhaustiveness argument: E = dim eps*H1 and g = dim ((eps)+(A,B))/(A,B) are
invariant under (A, B) -> (uA, vB) for units u, v (the complex isomorphism
psi_2 = u, psi_1 = diag(u, 1) resp. diag(1, v), psi_0 = 1 commutes with eps
since units are central) and under the swap (A, B) -> (B, A) (A12 §7).  So
checking one representative per unit-orbit pair (unordered) covers ALL
|T|^2 pairs.  Orbits are found by BFS with generator multiplications; if
the generator set under-generates the unit group the only effect is orbit
FRAGMENTATION — more representatives than needed — which costs time, never
coverage.  The script also self-checks the invariance empirically (random
unit rescalings must preserve (E, g)) and cross-checks total weighted pair
counts against |T|^2.

Strata (every order-2 deck s in each):
  F2[Z16], F2[Z8xZ2], F2[Z4xZ4]      (the OQ2 danger zone, |P| = 16)
  F4[Z8],  F4[Z4xZ2]                 (|P| = 8, previously random-only)
  F8[Z2],  F8[Z4],  F8[Z2x Z2]       (untouched residue field)

F8[Z2] was already swept exhaustively pair-by-pair in session 0; here it
doubles as a validator for the orbit machinery (same conclusion, and the
weighted g>0 counts must be consistent).

Run:  python3 scripts/a13_orbit_exhaustive_sweep.py [names...]
      (no args = all strata, sequential; pass stratum names to shard, e.g.
       `python3 ... F2[Z8xZ2] F2[Z4xZ4]` — names as printed in the output)
"""

import sys
import time

from a13_bockstein_stratified_sweep import (
    BlockAlgebra, apply_cols, check_pair, element_form_check, rank_of,
    reduce_vec, rref_add, tower_lift_check)
import random


# ---------- unit-orbit machinery ----------

def unit_generators(alg):
    """Multiplication matrices for a generating-ish set of units.

    Field scalar gen (if d > 1), the group monomials, and 1 + m_i for every
    F2-basis element m_i of the augmentation ideal span{w^e (1+p) : p != 1}.
    Under-generation only fragments orbits (safe); the invariance self-check
    plus the F8[Z2] cross-validation guard correctness.
    """
    gens = []
    if alg.d > 1:
        gens.append(alg.elt_matrix(alg.monomial(1, 0, 0)))  # times omega
    one = alg.monomial(0, 0, 0)
    for i in range(alg.pa):
        for j in range(alg.pb):
            if (i, j) == (0, 0):
                continue
            gens.append(alg.elt_matrix(alg.monomial(0, i, j)))  # times x^i y^j
            for e in range(alg.d):
                m = alg.monomial(e, 0, 0) ^ alg.monomial(e, i, j)  # w^e(1+p)
                gens.append(alg.elt_matrix(one ^ m))              # 1 + m
    return gens


def unit_orbits(alg):
    """Partition all 2^n elements into unit-orbit components (BFS).

    Returns (reps, sizes): representative (minimum) and size per component.
    """
    n_elts = 1 << alg.n
    gens = unit_generators(alg)
    seen = bytearray(n_elts)
    reps, sizes = [], []
    for start in range(n_elts):
        if seen[start]:
            continue
        comp = [start]
        seen[start] = 1
        frontier = [start]
        while frontier:
            nxt = []
            for v in frontier:
                for gm in gens:
                    w = apply_cols(gm, v)
                    if not seen[w]:
                        seen[w] = 1
                        comp.append(w)
                        nxt.append(w)
            frontier = nxt
        reps.append(min(comp))
        sizes.append(len(comp))
    return reps, sizes


def invariance_selfcheck(alg, eps_cols, reps, trials=40):
    """Random unit rescalings must preserve (E, g)."""
    units = [r for r, in []]  # placeholder to appease linters
    del units
    rng = random.Random(1300 + alg.n)
    # collect some units: BFS component of 1 is the unit group; sample by
    # random generator words applied to 1
    gens = unit_generators(alg)
    one = alg.monomial(0, 0, 0)

    def rand_unit():
        v = one
        for _ in range(rng.randrange(1, 8)):
            v = apply_cols(gens[rng.randrange(len(gens))], v)
        return v

    for _ in range(trials):
        A = reps[rng.randrange(len(reps))]
        B = rng.getrandbits(alg.n)
        u, v = rand_unit(), rand_unit()
        E1, g1 = check_pair(alg, alg.elt_matrix(A), alg.elt_matrix(B),
                            eps_cols)
        E2, g2 = check_pair(alg, alg.elt_matrix(alg.mul(u, A)),
                            alg.elt_matrix(alg.mul(v, B)), eps_cols)
        assert (E1, g1) == (E2, g2), (
            f"INVARIANCE FAILURE: A={A:#x} B={B:#x} u={u:#x} v={v:#x} "
            f"({E1},{g1}) != ({E2},{g2})")


def sweep_stratum(name, alg, s_ij):
    t0 = time.time()
    eps = alg.monomial(0, 0, 0) ^ alg.monomial(0, *s_ij)
    eps_cols = alg.elt_matrix(eps)
    eps_im = []
    for c in eps_cols:
        rref_add(eps_im, c)

    ok, r1, r3, nn = tower_lift_check(alg.pa, alg.pb, alg.d, s_ij)
    assert ok, f"tower-lift rank failure on {name} s={s_ij}"

    reps, sizes = unit_orbits(alg)
    invariance_selfcheck(alg, eps_cols, reps)
    n_reps = len(reps)
    total_weight = sum(sizes)
    assert total_weight == 1 << alg.n

    MAs = [alg.elt_matrix(r) for r in reps]
    live_flags = [reduce_vec(eps_im, r) != 0 for r in reps]

    n_pairs = w_pairs = w_gap = w_live = 0
    violations = []
    max_defect = 0
    for i in range(n_reps):
        for j in range(i, n_reps):
            E, g = check_pair(alg, MAs[i], MAs[j], eps_cols)
            n_pairs += 1
            w = sizes[i] * sizes[j] * (2 if i != j else 1)
            w_pairs += w
            if g > 0:
                w_gap += w
                if live_flags[i] and live_flags[j]:
                    w_live += w
            defect = E - 2 * g
            if defect < 0 or (g == 0 and E > 0):
                violations.append(("THEOREM", reps[i], reps[j], E, g))
            elif defect > 0:
                max_defect = max(max_defect, defect)
                violations.append(("CONJ-EQ", reps[i], reps[j], E, g))
    # weighted totals must reconstruct the full ordered-pair space
    assert w_pairs == (1 << alg.n) ** 2

    status = "OK" if not violations else f"{len(violations)} VIOLATIONS"
    print(f"{name:12s} s={s_ij} orbits={n_reps:>5d} rep-pairs={n_pairs:>9d} "
          f"[= {w_pairs:.3e} weighted] g>0:{w_gap:.3e} live:{w_live:.3e} "
          f"maxdef={max_defect} {status} ({time.time() - t0:.0f}s)",
          flush=True)
    for kind, A, B, E, g in violations[:10]:
        print(f"    !! {kind}: A={A:#x} B={B:#x} E={E} g={g}")
    return violations


STRATA = [
    ("F8[Z2]", (2, 1, 3)),
    ("F8[Z4]", (4, 1, 3)),
    ("F8[Z2xZ2]", (2, 2, 3)),
    ("F4[Z8]", (8, 1, 2)),
    ("F4[Z4xZ2]", (4, 2, 2)),
    ("F2[Z16]", (16, 1, 1)),
    ("F2[Z8xZ2]", (8, 2, 1)),
    ("F2[Z4xZ4]", (4, 4, 1)),
]


def main():
    wanted = sys.argv[1:]
    all_violations = []
    for name, (pa, pb, d) in STRATA:
        if wanted and name not in wanted:
            continue
        alg = BlockAlgebra(pa, pb, d)
        for s_ij in alg.order2_elements():
            all_violations += sweep_stratum(name, alg, s_ij)
    print()
    if all_violations:
        print(f"TOTAL VIOLATIONS: {len(all_violations)}")
    else:
        print("ALL STRATA EXHAUSTIVELY CLEAN (E = 2g on every unit-orbit "
              "pair = every (A,B) pair; theorems hold everywhere).")


if __name__ == "__main__":
    main()
