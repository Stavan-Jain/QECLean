"""Tests for the canonical predicate vocabulary.

Validates that each predicate evaluates correctly on the Bravyi-table
codes (using the actual polynomials from `instances/bravyi_table.yaml`)
and that the axis-pinning mapping in `predicates.AXES` is consistent
with the predicate set.
"""

from __future__ import annotations

import pytest

from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.predicates import (
    AXES,
    PREDICATES,
    check_all_predicates,
    check_predicate,
    get_axis,
    list_predicates,
    pinned_axes,
    unpinned_axes,
)


# Bravyi-table polynomials (from instances/bravyi_table.yaml).
BRAVYI_INSTANCES = {
    "bb_72_12_6":      ((6, 6),  "x^3 + y + y^2", "y^3 + x + x^2"),
    "bb_90_8_10":      ((15, 3), "x^9 + y + y^2", "1 + x^2 + x^7"),
    "bb_108_8_10":     ((9, 6),  "x^3 + y + y^2", "y^3 + x + x^2"),
    "gross":           ((12, 6), "x^3 + y + y^2", "y^3 + x + x^2"),
    "bb_288_12_18":    ((12, 12),"x^3 + y^2 + y^7","y^3 + x + x^2"),
}


def _load(name: str):
    (ell, m), a_str, b_str = BRAVYI_INSTANCES[name]
    G = ZmZn(ell, m)
    return G, Poly.from_string(a_str, G), Poly.from_string(b_str, G)


# --- registry sanity ---------------------------------------------------------


def test_predicates_registered_under_unique_names() -> None:
    assert len(PREDICATES) == len(set(PREDICATES))


def test_list_predicates_includes_round1_set() -> None:
    names = set(list_predicates())
    expected = {
        "elem_ab_G_odd",
        "strict_elem_ab_G_odd",
        "single_prime_G_odd",
        "multi_prime_G_odd",
        "G_odd_all_rank_1",
        "G_odd_mixed_rank",
        "G_2_trivial",
        "G_2_elem_ab",
        "non_semisimple_F2G",
        "non_degenerate",
        "degenerate",
        "c_geq_2",
        "c_geq_3",
        "c_eq_3_exact",
        "odd_weight_A",
        "odd_weight_B",
        "joint_vanishing_nonempty",
    }
    assert expected.issubset(names)


def test_check_predicate_unknown_name_raises() -> None:
    G, A, B = _load("gross")
    with pytest.raises(KeyError):
        check_predicate("not_a_predicate", G, A, B)


# --- group-structure predicates on Bravyi instances --------------------------


def test_gross_has_strict_elem_ab_G_odd_single_prime_mixed_rank() -> None:
    """gross has G = Z_12 × Z_6, G_odd = Z_3 × Z_3 (single prime 3, rank 2).
    Should classify as strict elem-ab + single-prime + mixed-rank."""
    G, A, B = _load("gross")
    assert check_predicate("elem_ab_G_odd", G, A, B) is True
    assert check_predicate("strict_elem_ab_G_odd", G, A, B) is True
    assert check_predicate("single_prime_G_odd", G, A, B) is True
    assert check_predicate("multi_prime_G_odd", G, A, B) is False
    assert check_predicate("G_odd_mixed_rank", G, A, B) is True
    assert check_predicate("G_odd_all_rank_1", G, A, B) is False


def test_bb_90_has_multi_prime_mixed_rank_G_odd() -> None:
    """bb_90: G = Z_15 × Z_3, G_odd = Z_3 × Z_5 × Z_3 = Z_3² × Z_5.
    Multi-prime (3 and 5) with 3-rank 2, 5-rank 1 — the R1+R4 failure
    regime by group structure."""
    G, A, B = _load("bb_90_8_10")
    assert check_predicate("multi_prime_G_odd", G, A, B) is True
    assert check_predicate("single_prime_G_odd", G, A, B) is False
    assert check_predicate("G_odd_mixed_rank", G, A, B) is True
    assert check_predicate("elem_ab_G_odd", G, A, B) is True
    assert check_predicate("strict_elem_ab_G_odd", G, A, B) is False


def test_bb_108_has_non_elem_ab_G_odd() -> None:
    """bb_108: G = Z_9 × Z_6, G_odd = Z_9 × Z_3. The Z_9 factor is cyclic
    of order 9 (NOT Z_3 × Z_3), so G_odd is non-elem-ab."""
    G, A, B = _load("bb_108_8_10")
    assert check_predicate("elem_ab_G_odd", G, A, B) is False
    assert check_predicate("strict_elem_ab_G_odd", G, A, B) is False
    assert check_predicate("single_prime_G_odd", G, A, B) is True  # only 3


def test_bb_90_is_G_2_trivial() -> None:
    """bb_90 has |G| = 45 = 3²·5 (odd), so G_2 is trivial — the §6j
    exception (F_2[G] semisimple)."""
    G, A, B = _load("bb_90_8_10")
    assert check_predicate("G_2_trivial", G, A, B) is True
    assert check_predicate("non_semisimple_F2G", G, A, B) is False


def test_gross_is_non_semisimple() -> None:
    """gross has |G| = 72 = 2³·3² (even), so F_2[G] is non-semisimple
    (§6j fires)."""
    G, A, B = _load("gross")
    assert check_predicate("G_2_trivial", G, A, B) is False
    assert check_predicate("non_semisimple_F2G", G, A, B) is True


# --- degeneracy on Bravyi instances ------------------------------------------


def test_all_bravyi_codes_are_degenerate_with_c_geq_3() -> None:
    """Every Bravyi-table code has c = 3 (HANDOFF.md §6i fingerprint)."""
    for name in BRAVYI_INSTANCES:
        G, A, B = _load(name)
        assert check_predicate("degenerate", G, A, B) is True, f"{name}"
        assert check_predicate("non_degenerate", G, A, B) is False, f"{name}"
        assert check_predicate("c_geq_2", G, A, B) is True, f"{name}"
        assert check_predicate("c_geq_3", G, A, B) is True, f"{name}"
        assert check_predicate("c_eq_3_exact", G, A, B) is True, f"{name}: c should be exactly 3"


def test_G_2_elem_ab_on_bravyi_codes() -> None:
    """bb_72 has G = Z_6 × Z_6: 2-Sylow is Z_2 × Z_2 — elem-ab.
    gross has G = Z_12 × Z_6: 2-Sylow contains Z_4 — NOT elem-ab.
    bb_90 has G = Z_15 × Z_3: 2-Sylow trivial — vacuously elem-ab."""
    G, A, B = _load("bb_72_12_6")
    assert check_predicate("G_2_elem_ab", G, A, B) is True
    G, A, B = _load("gross")
    assert check_predicate("G_2_elem_ab", G, A, B) is False
    G, A, B = _load("bb_90_8_10")
    # G_2 trivial → trivially elem_ab (the empty 2-Sylow is (Z_2)^0)
    assert check_predicate("G_2_elem_ab", G, A, B) is True


def test_joint_vanishing_nonempty_on_gross() -> None:
    """gross is known to have joint-vanishing orbits (HANDOFF_C2 §5;
    the C-v2 conjecture wouldn't have been written otherwise)."""
    G, A, B = _load("gross")
    assert check_predicate("joint_vanishing_nonempty", G, A, B) is True


# --- polynomial parity on Bravyi instances -----------------------------------


def test_gross_polynomials_are_odd_weight() -> None:
    G, A, B = _load("gross")
    assert A.weight() == 3 and B.weight() == 3
    assert check_predicate("odd_weight_A", G, A, B) is True
    assert check_predicate("odd_weight_B", G, A, B) is True


# --- check_all_predicates -----------------------------------------------------


def test_check_all_predicates_conjunction() -> None:
    G, A, B = _load("gross")
    # gross satisfies all of these:
    sat = {"elem_ab_G_odd", "c_geq_3", "odd_weight_A", "odd_weight_B"}
    assert check_all_predicates(sat, G, A, B) is True
    # And does NOT satisfy these (non_degenerate fails):
    unsat = {"non_degenerate"}
    assert check_all_predicates(unsat, G, A, B) is False


# --- axis vocabulary ---------------------------------------------------------


def test_pinned_axes_for_r1_r4_hypothesis() -> None:
    """The R1+R4 hypothesis pins these axes (per HANDOFF_R2.md §4.4):
    G_odd_elem_ab_class, c_value, A_parity, B_parity."""
    hyp = {"elem_ab_G_odd", "c_geq_3", "odd_weight_A", "odd_weight_B"}
    pinned = pinned_axes(hyp)
    assert pinned == {
        "G_odd_elem_ab_class",
        "c_value",
        "A_parity",
        "B_parity",
    }


def test_unpinned_axes_for_r1_r4_hypothesis() -> None:
    """The R1+R4 hypothesis leaves prime_structure / rank_profile /
    G_2_shape / joint_vanishing unpinned — the axes the falsifier
    exploited."""
    hyp = {"elem_ab_G_odd", "c_geq_3", "odd_weight_A", "odd_weight_B"}
    unpinned = unpinned_axes(hyp)
    assert "prime_structure" in unpinned
    assert "prime_rank_profile" in unpinned
    assert "G_2_shape" in unpinned
    assert "joint_vanishing" in unpinned


def test_joint_vanishing_predicate_pins_joint_vanishing_axis() -> None:
    """Adding `joint_vanishing_nonempty` to a hypothesis should pin
    the joint_vanishing axis (so adversarial generation skips it)."""
    hyp_without = {"elem_ab_G_odd"}
    hyp_with = hyp_without | {"joint_vanishing_nonempty"}
    assert "joint_vanishing" in unpinned_axes(hyp_without)
    assert "joint_vanishing" not in unpinned_axes(hyp_with)


def test_G_2_elem_ab_predicate_pins_G_2_shape_axis() -> None:
    """`G_2_elem_ab` should pin the G_2_shape axis (it asserts the
    `elem_ab` value)."""
    assert "G_2_shape" in unpinned_axes(set())
    assert "G_2_shape" not in unpinned_axes({"G_2_elem_ab"})


def test_empty_hypothesis_leaves_all_axes_unpinned() -> None:
    assert unpinned_axes(set()) == {axis.name for axis in AXES}


def test_get_axis_unknown_name_raises() -> None:
    with pytest.raises(KeyError):
        get_axis("not_an_axis")


def test_each_axis_has_nonempty_range() -> None:
    for axis in AXES:
        assert len(axis.range_values) >= 2, f"axis {axis.name}"


def test_axis_pinning_predicates_all_registered() -> None:
    """Every predicate listed in any axis's `pinned_by_predicates` set
    must be a registered predicate."""
    registered = set(list_predicates())
    for axis in AXES:
        unknown = axis.pinned_by_predicates - registered
        assert not unknown, (
            f"axis {axis.name} references unregistered predicates: {unknown}"
        )
