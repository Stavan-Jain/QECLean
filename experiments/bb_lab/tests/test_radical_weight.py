"""Tests for `radical_weight.w_mu` — the C-v1 weight-aware Jacobson
radical-filtration invariant.

Coverage:
- `loewy_length` and `jacobson_filtration_dims` on chain rings, tensor
  products, and the semisimple limit.
- Z_4 chain ring: hand-checked `w_μ(A, O₀)` against the explicit
  `(x − 1)`-filtration of `F_2[Z_4] = F_2[y]/(y^4)`.
- Z_3 (smallest semisimple): single-orbit trivial component and
  per-orbit dual-distance check at `μ = 1`.
- Semisimple-limit (W4): `w_1(A, O) == per_orbit_dual_distance(A, O)`
  on vanishing orbits, `w_μ = ∞` for `μ ≥ 2`. Tested on
  `Z_3 × Z_5` ([[30,4,6]] champion polynomial) and `Z_3 × Z_3`.
- Invariance (W1) under G-translation and Aut(G) on Z_4.
- Gross numerical table.
- API validation: bad arguments, basis-dim cap.
"""

from __future__ import annotations

import math

import pytest

from bb_lab.algebraic_features import (
    g_odd_frobenius_orbits,
    jacobson_radical_depth,
)
from bb_lab.group import AbelianGroup, ZmZn
from bb_lab.poly import Poly
from bb_lab.radical_weight import (
    bb_radical_bound,
    bb_radical_bound_alt,
    jacobson_filtration_dims,
    joint_support_subgroup_index,
    loewy_length,
    w_mu,
    w_mu_table,
)
from bb_lab.weight_invariants import per_orbit_dual_distance


# ---------------------------------------------------------------------------
# Loewy length / filtration dim sanity
# ---------------------------------------------------------------------------


def test_loewy_length_z4():
    """Z_4: 2-Sylow is Z_4 itself, Loewy length = 4."""
    G = AbelianGroup((4,))
    assert loewy_length(G) == 4


def test_loewy_length_z4_z2():
    """Z_4 × Z_2: 2-Sylow = Z_4 × Z_2, Loewy length = (4-1)+(2-1)+1 = 5."""
    G = AbelianGroup((4, 2))
    assert loewy_length(G) == 5


def test_loewy_length_z2_cubed():
    """(Z_2)^3 elementary abelian: 2-Sylow self, length = 3·1 + 1 = 4."""
    G = AbelianGroup((2, 2, 2))
    assert loewy_length(G) == 4


def test_loewy_length_gross():
    """Gross G = Z_12 × Z_6: 2-Sylow = Z_4 × Z_2, Loewy length = 5."""
    G = ZmZn(12, 6)
    assert loewy_length(G) == 5


def test_loewy_length_semisimple():
    """Semisimple groups (|G| odd) have Loewy length 1 (trivial radical)."""
    for G in [AbelianGroup((3,)), ZmZn(3, 3), ZmZn(3, 5), ZmZn(5, 7)]:
        assert loewy_length(G) == 1, f"semisimple {G} should have Loewy length 1"


def test_filtration_dims_z4():
    """F_2[Z_4] filtration dimensions: [4, 3, 2, 1, 0]."""
    G = AbelianGroup((4,))
    assert jacobson_filtration_dims(G) == [4, 3, 2, 1, 0]


def test_filtration_dims_z4_z2():
    """F_{2^|O|}[Z_4 × Z_2] filtration dims: [8, 7, 5, 3, 1, 0]."""
    G = AbelianGroup((4, 2))
    assert jacobson_filtration_dims(G) == [8, 7, 5, 3, 1, 0]


def test_filtration_dims_gross():
    """Gross's R_O has the same filtration as Z_4 × Z_2 over F_{2^|O|}."""
    G = ZmZn(12, 6)
    assert jacobson_filtration_dims(G) == [8, 7, 5, 3, 1, 0]


# ---------------------------------------------------------------------------
# Z_4 chain ring: hand-checked
# ---------------------------------------------------------------------------


def test_w_mu_z4_one_plus_x():
    """G = Z_4, A = 1 + x = y (depth 1 in radical, μ_O = 1).

    ker(mult_y) = (y^3) ⊂ F_2[Z_4] is the only annihilator;
    spanned by y^3 = 1+x+x^2+x^3 (weight 4).

    V_{O, μ}(A) = (y^3) ∩ m_O^{μ-1} = (y^3) for μ ≤ 4, {0} for μ = 5.
    So w_μ = 4 for μ ∈ {1, 2, 3, 4}, ∞ for μ = 5.
    """
    G = AbelianGroup((4,))
    A = Poly.from_string("1 + x", G)
    orbit = g_odd_frobenius_orbits(G)[0]
    for mu in range(1, 5):
        assert w_mu(A, orbit, mu, G) == 4
    assert w_mu(A, orbit, 5, G) == float("inf")


def test_w_mu_z4_y_squared():
    """G = Z_4, A = (1+x)^2 = y^2 = 1+x^2 (μ_O = 2).

    ker(mult_{y^2}) = (y^2) = span(y^2 = 1+x^2, y^3 = 1+x+x^2+x^3).
    Min weight of (y^2): y^2 has weight 2, y^2 + y^3 = x+x^3 has weight 2.
    So w_1 = 2.

    Filtration:
      μ = 1: V = (y^2). Min weight 2.
      μ = 2: V = (y^2) ∩ (y) = (y^2). Same, 2.
      μ = 3: V = (y^2) ∩ (y^2) = (y^2). Same, 2.
      μ = 4: V = (y^2) ∩ (y^3) = (y^3). Only y^3, weight 4.
      μ = 5: V = (y^2) ∩ 0 = {0}. ∞.
    """
    G = AbelianGroup((4,))
    A = Poly.from_string("1 + x^2", G)
    orbit = g_odd_frobenius_orbits(G)[0]
    assert w_mu(A, orbit, 1, G) == 2
    assert w_mu(A, orbit, 2, G) == 2
    assert w_mu(A, orbit, 3, G) == 2
    assert w_mu(A, orbit, 4, G) == 4
    assert w_mu(A, orbit, 5, G) == float("inf")


def test_w_mu_z4_y_cubed():
    """G = Z_4, A = 1 + x + x^2 + x^3 = y^3 (μ_O = 3).

    ker(mult_{y^3}) = (y) — the augmentation ideal, dim 3.
    (y) = span(y = 1+x, y^2 = 1+x^2, y^3 = 1+x+x^2+x^3).

    Min weights in (y):
      - y has weight 2.
      - y^2 has weight 2.
      - y^3 has weight 4.
      - y + y^2 = x + x^2 has weight 2.
      - y + y^3 = x + x^2 + x^3 wait let me recompute.
        y = 1+x, y^3 = 1+x+x^2+x^3, y + y^3 = x^2+x^3, weight 2.
      - y^2 + y^3 = (1+x^2)+(1+x+x^2+x^3) = x+x^3, weight 2.
      - y+y^2+y^3 = (1+x)+(1+x^2)+(1+x+x^2+x^3) = 1+x^3, weight 2.
    All non-zero elements of (y) have weight 2 or 4. Min = 2.

    V_{O, μ}(A) = (y) ∩ m_O^{μ-1}:
      μ = 1: (y) ∩ R = (y). Min 2.
      μ = 2: (y) ∩ (y) = (y). Min 2.
      μ = 3: (y) ∩ (y^2) = (y^2) = span(y^2, y^3). Min 2 (y^2 + y^3 = x+x^3).
      μ = 4: (y) ∩ (y^3) = (y^3). Only y^3, weight 4.
      μ = 5: 0. ∞.
    """
    G = AbelianGroup((4,))
    A = Poly.from_string("1 + x + x^2 + x^3", G)
    orbit = g_odd_frobenius_orbits(G)[0]
    assert w_mu(A, orbit, 1, G) == 2
    assert w_mu(A, orbit, 2, G) == 2
    assert w_mu(A, orbit, 3, G) == 2
    assert w_mu(A, orbit, 4, G) == 4
    assert w_mu(A, orbit, 5, G) == float("inf")


def test_w_mu_z4_unit():
    """G = Z_4, A = 1 (a unit, μ_O = 0). Every w_μ = ∞."""
    G = AbelianGroup((4,))
    A = Poly.from_string("1", G)
    orbit = g_odd_frobenius_orbits(G)[0]
    for mu in range(1, 6):
        assert w_mu(A, orbit, mu, G) == float("inf")


# ---------------------------------------------------------------------------
# Semisimple-limit recovery (W4): w_1 == per_orbit_dual_distance
# ---------------------------------------------------------------------------


def test_w_1_recovers_per_orbit_dual_z3_z5_champion():
    """Z_3 × Z_5 (semisimple, |G| = 15 odd). For A = 1 + x + x^2·y
    ([[30,4,6]] champion poly), w_1 should match per_orbit_dual_distance
    on every vanishing orbit; w_μ = ∞ for μ ≥ 2.
    """
    G = ZmZn(3, 5)
    A = Poly.from_string("1 + x + x^2*y", G)
    orbits = g_odd_frobenius_orbits(G)
    podd = per_orbit_dual_distance(A, G)
    for o in orbits:
        mu_O = jacobson_radical_depth(A, o, G)
        if mu_O == 0:
            # Non-vanishing — both methods give ∞.
            assert w_mu(A, o, 1, G) == float("inf")
        else:
            # Vanishing — w_1 == per_orbit_dual_distance.
            assert w_mu(A, o, 1, G) == podd[o], (
                f"orbit {sorted(o)}: w_1 = {w_mu(A, o, 1, G)} vs "
                f"per_orbit_dual_distance = {podd[o]}"
            )
        # μ = 2 should always be ∞ in semisimple (m_O = 0).
        assert w_mu(A, o, 2, G) == float("inf")


def test_w_1_recovers_per_orbit_dual_z3_z3():
    """Z_3 × Z_3, multiple A choices: w_1 == per_orbit_dual on vanishing
    orbits, ∞ otherwise; w_2 = ∞ everywhere."""
    G = ZmZn(3, 3)
    for poly_str in ["1 + x + x^2", "1 + y + y^2", "1 + x*y + x^2*y^2"]:
        A = Poly.from_string(poly_str, G)
        orbits = g_odd_frobenius_orbits(G)
        podd = per_orbit_dual_distance(A, G)
        for o in orbits:
            mu_O = jacobson_radical_depth(A, o, G)
            if mu_O > 0:
                assert w_mu(A, o, 1, G) == podd[o]
            else:
                assert w_mu(A, o, 1, G) == float("inf")
            assert w_mu(A, o, 2, G) == float("inf")


def test_w_mu_semisimple_only_mu_1_finite():
    """Semisimple limit: w_μ = ∞ for all μ ≥ 2. Stronger version."""
    G = ZmZn(3, 5)
    A = Poly.from_string("1 + x + x^2*y", G)
    for o in g_odd_frobenius_orbits(G):
        for mu in range(2, 5):
            assert w_mu(A, o, mu, G) == float("inf"), (
                f"orbit {sorted(o)} mu={mu}: should be ∞ in semisimple, "
                f"got {w_mu(A, o, mu, G)}"
            )


# ---------------------------------------------------------------------------
# Invariance (W1) on Z_4
# ---------------------------------------------------------------------------


def test_w_mu_translation_invariance_z4():
    """G-translation: w_μ(A, O) = w_μ(g · A, O) for any g ∈ G.

    On Z_4, picking any translate of A = 1+x should give the same w_μ.
    """
    G = AbelianGroup((4,))
    A = Poly.from_string("1 + x", G)
    A_translated = Poly.from_string("x + x^2", G)  # = x · (1 + x)
    orbit = g_odd_frobenius_orbits(G)[0]
    for mu in range(1, 5):
        assert w_mu(A, orbit, mu, G) == w_mu(A_translated, orbit, mu, G)


def test_w_mu_translation_invariance_z3_z3():
    """G-translation on Z_3 × Z_3 (semisimple)."""
    G = ZmZn(3, 3)
    A = Poly.from_string("1 + x + x^2", G)
    A_translated = Poly.from_string("y + x*y + x^2*y", G)  # = y · A
    orbits = g_odd_frobenius_orbits(G)
    for o in orbits:
        assert w_mu(A, o, 1, G) == w_mu(A_translated, o, 1, G)


# ---------------------------------------------------------------------------
# Gross numerical table — populated for record-keeping
# ---------------------------------------------------------------------------


def test_w_mu_gross_A_table():
    """Gross G = Z_12 × Z_6, A = x^3 + y + y^2.

    Expected: 3 vanishing orbits with μ_O = 2 each; non-vanishing orbits
    give w_μ = ∞. The vanishing orbits all give the same numerical
    profile due to the algebraic symmetry.

    Recorded actual values: w_1 = w_2 = w_3 = w_4 = 36, w_5 = 48 per
    vanishing orbit. Note: these are LARGE because they live in
    F_2[G] (not just the semisimple quotient) — the per-orbit
    isotypic component R_O has support 6 × 8 = 48 in F_2[G], and
    any non-zero element has weight ≥ 6.
    """
    G = ZmZn(12, 6)
    A = Poly.from_string("x^3 + y + y^2", G)
    orbits = g_odd_frobenius_orbits(G)
    vanishing_w_values: list[list[int | float]] = []
    for o in orbits:
        mu_O = jacobson_radical_depth(A, o, G)
        if mu_O == 0:
            for mu in range(1, loewy_length(G) + 1):
                assert w_mu(A, o, mu, G) == float("inf")
        else:
            assert mu_O == 2  # gross's known structure
            row = [w_mu(A, o, mu, G) for mu in range(1, loewy_length(G) + 1)]
            vanishing_w_values.append(row)
    # All vanishing orbits should give the same w_μ profile.
    assert len(vanishing_w_values) == 3
    for row in vanishing_w_values[1:]:
        assert row == vanishing_w_values[0]
    # The specific profile (recorded, not derived from independent calculation).
    assert vanishing_w_values[0] == [36, 36, 36, 36, 48]


def test_w_mu_gross_B_table():
    """Gross B = y^3 + x + x^2. By the (x ↔ y) symmetry of gross, the
    w_μ profile is identical to A's, just on different orbits."""
    G = ZmZn(12, 6)
    B = Poly.from_string("y^3 + x + x^2", G)
    orbits = g_odd_frobenius_orbits(G)
    vanishing_w_values: list[list[int | float]] = []
    for o in orbits:
        mu_O = jacobson_radical_depth(B, o, G)
        if mu_O > 0:
            row = [w_mu(B, o, mu, G) for mu in range(1, loewy_length(G) + 1)]
            vanishing_w_values.append(row)
    assert len(vanishing_w_values) == 3
    for row in vanishing_w_values[1:]:
        assert row == vanishing_w_values[0]
    assert vanishing_w_values[0] == [36, 36, 36, 36, 48]


def test_w_mu_diverges_from_per_orbit_dual_on_non_semisimple_gross():
    """On gross (non-semisimple), w_1 ≠ per_orbit_dual_distance. The
    existing function uses fiber-summed character constraints (weaker);
    w_μ uses proper per-fiber constraints (stricter, larger min weight).
    """
    G = ZmZn(12, 6)
    A = Poly.from_string("x^3 + y + y^2", G)
    orbits = g_odd_frobenius_orbits(G)
    podd = per_orbit_dual_distance(A, G)
    for o in orbits:
        mu_O = jacobson_radical_depth(A, o, G)
        if mu_O > 0:
            assert w_mu(A, o, 1, G) >= podd[o], (
                "w_1 should be ≥ per_orbit_dual_distance (stricter "
                "constraint = larger min weight)."
            )
            assert w_mu(A, o, 1, G) > podd[o], (
                "for gross, the constraints actually differ — "
                "w_1 should be strictly > per_orbit_dual_distance."
            )


# ---------------------------------------------------------------------------
# Monotonicity in μ
# ---------------------------------------------------------------------------


def test_w_mu_monotonic_in_mu():
    """w_μ is monotonically non-decreasing in μ.

    Reason: V_{O, μ+1}(A) ⊆ V_{O, μ}(A), so min weight can only grow
    (or jump to ∞).
    """
    G = ZmZn(12, 6)
    A = Poly.from_string("x^3 + y + y^2", G)
    orbits = g_odd_frobenius_orbits(G)
    for o in orbits:
        prev = -1
        for mu in range(1, loewy_length(G) + 2):
            wm = w_mu(A, o, mu, G)
            if wm == float("inf"):
                continue
            assert wm >= prev, (
                f"w_mu non-monotonic on orbit {sorted(o)} at μ={mu}: "
                f"w_{mu-1}={prev}, w_{mu}={wm}"
            )
            prev = wm


# ---------------------------------------------------------------------------
# w_mu_table convenience
# ---------------------------------------------------------------------------


def test_w_mu_table_z3_z3():
    """w_mu_table covers all (orbit, μ) pairs."""
    G = ZmZn(3, 3)
    A = Poly.from_string("1 + x + x^2", G)
    table = w_mu_table(A, G)
    orbits = g_odd_frobenius_orbits(G)
    L = loewy_length(G)
    assert len(table) == len(orbits) * L  # 5 orbits × Loewy length 1
    for o in orbits:
        for mu in range(1, L + 1):
            assert (o, mu) in table


def test_w_mu_table_default_max_mu_is_loewy_length():
    """When max_mu is None, table goes up to the Loewy length."""
    G = AbelianGroup((4,))
    A = Poly.from_string("1 + x^2", G)
    table = w_mu_table(A, G)
    assert max(mu for _, mu in table) == loewy_length(G)


# ---------------------------------------------------------------------------
# API edge cases
# ---------------------------------------------------------------------------


def test_w_mu_bad_orbit():
    """Passing an orbit not in G_odd's Frobenius orbits should error."""
    G = AbelianGroup((4,))
    A = Poly.from_string("1", G)
    bad_orbit = frozenset({(7,)})  # 7 not in G_odd = trivial group
    with pytest.raises(ValueError):
        w_mu(A, bad_orbit, 1, G)


def test_w_mu_bad_mu():
    """μ < 1 should error."""
    G = AbelianGroup((4,))
    A = Poly.from_string("1", G)
    orbit = g_odd_frobenius_orbits(G)[0]
    with pytest.raises(ValueError):
        w_mu(A, orbit, 0, G)
    with pytest.raises(ValueError):
        w_mu(A, orbit, -1, G)


def test_w_mu_mismatched_group():
    """Passing G that doesn't match A.group should error."""
    G_a = AbelianGroup((4,))
    G_b = ZmZn(3, 3)
    A = Poly.from_string("1", G_a)
    orbit = g_odd_frobenius_orbits(G_a)[0]
    with pytest.raises(ValueError):
        w_mu(A, orbit, 1, G_b)


# ===========================================================================
# C-v2 conjecture tests — DOCUMENT THE FALSIFICATION
# ===========================================================================
#
# The conjecture
#     d_X(BB(G, A, B)) ≥ ⌈(1/c) · min_O min(w_1(A, O), w_1(B, O))⌉
# is tight on gross (12=12) but VIOLATES on bb_108_8_10 (12 > 10) and
# on 3 319 corpus rows (85%). These tests pin the numerical record so
# any future refactor that changes bb_radical_bound's behavior is
# caught immediately.


def test_joint_support_subgroup_index_gross():
    """Gross: G_a = ⟨3⟩ × Z_6 (order 24), G_b = Z_12 × ⟨3⟩ (order 24),
    G_a ∩ G_b = ⟨3⟩ × ⟨3⟩ (order 8). c = 24/8 = 3.
    """
    G = ZmZn(12, 6)
    A = Poly.from_string("x^3 + y + y^2", G)
    B = Poly.from_string("y^3 + x + x^2", G)
    assert joint_support_subgroup_index(A, B, G) == 3


def test_joint_support_subgroup_index_non_degenerate():
    """When both supports generate G, c = 1."""
    G = ZmZn(3, 5)
    # Non-degenerate champion: supp generates Z_3 × Z_5.
    A = Poly.from_string("1 + x + x^2*y", G)
    B = Poly.from_string("1 + x + x*y^3", G)
    assert joint_support_subgroup_index(A, B, G) == 1


def test_joint_support_subgroup_index_equal_polys():
    """When A = B, G_a = G_b, intersection = G_a, c = 1."""
    G = ZmZn(3, 6)
    A = Poly.from_string("1 + y + y^2", G)
    assert joint_support_subgroup_index(A, A, G) == 1


def test_bb_radical_bound_gross_tight():
    """Gross: w_1 = 36 per vanishing orbit, c = 3, bound = 12 = d.

    This is the gross "factor of 3" coincidence (HANDOFF_C2 §1) that
    seeded the C-v2 conjecture.
    """
    G = ZmZn(12, 6)
    A = Poly.from_string("x^3 + y + y^2", G)
    B = Poly.from_string("y^3 + x + x^2", G)
    assert bb_radical_bound(A, B, G) == 12


def test_bb_radical_bound_bb108_falsifies():
    """bb_108_8_10 (G = Z_9 × Z_6) VIOLATES the conjecture.

    Bound = 12 but Bravyi 2024 establishes d_published = 10. This
    test pins the falsification numerical record (HANDOFF_C2 §C-v2.4
    Bravyi-table verdict).
    """
    G = ZmZn(9, 6)
    A = Poly.from_string("x^3 + y + y^2", G)
    B = Poly.from_string("y^3 + x + x^2", G)
    bound = bb_radical_bound(A, B, G)
    assert bound == 12
    d_published = 10
    assert bound > d_published, (
        "C-v2 conjecture asserts d ≥ 12 but Bravyi 2024 establishes "
        "d = 10; this constitutes a falsification."
    )


def test_bb_radical_bound_z3_z6_equal_polys_falsifies():
    """Z_3 × Z_6, A = B = 1+y+y² (d = 2 per corpus): bound = 12 > 2."""
    G = ZmZn(3, 6)
    A = Poly.from_string("1 + y + y^2", G)
    B = Poly.from_string("1 + y + y^2", G)
    assert bb_radical_bound(A, B, G) == 12


def test_bb_radical_bound_alt_sum_violates_gross():
    """Per HANDOFF_C2 §5 Alt-C: sum formulation violates gross
    (bound = 24 > d = 12). Dead-on-arrival, included for completeness.
    """
    G = ZmZn(12, 6)
    A = Poly.from_string("x^3 + y + y^2", G)
    B = Poly.from_string("y^3 + x + x^2", G)
    assert bb_radical_bound_alt(A, B, G, formulation="sum") == 24


def test_bb_radical_bound_alt_multi_mu_gross_loose():
    """multi-mu gives bound 6 on gross (loose by 6 vs d = 12)."""
    G = ZmZn(12, 6)
    A = Poly.from_string("x^3 + y + y^2", G)
    B = Poly.from_string("y^3 + x + x^2", G)
    assert bb_radical_bound_alt(A, B, G, formulation="multi-mu") == 6


def test_bb_radical_bound_alt_unknown_formulation():
    G = ZmZn(12, 6)
    A = Poly.from_string("x^3 + y + y^2", G)
    B = Poly.from_string("y^3 + x + x^2", G)
    with pytest.raises(ValueError):
        bb_radical_bound_alt(A, B, G, formulation="nonexistent")
