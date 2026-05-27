"""Tests for the parameterized adversarial stress-test generator.

Headline test: the R1+R4 hypothesis (`{elem_ab_G_odd, odd_weight_A,
odd_weight_B}`) yields mixed-rank multi-prime instances on the
Z_3 × Z_15 falsifier group. Every generated instance satisfies every
hypothesis predicate (the falsifier lives *inside* the hypothesis
domain, never outside it).
"""

from __future__ import annotations

import pytest

from bb_lab.adversarial import (
    StressTest,
    generate_stress_tests,
    supported_axis_value_pairs,
)
from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.predicates import check_all_predicates, unpinned_axes


def _reload(t: StressTest):
    G = ZmZn(t.ell, t.m)
    A = Poly.from_string(t.A_poly, G)
    B = Poly.from_string(t.B_poly, G)
    return G, A, B


# --- hypothesis preservation ------------------------------------------------


def test_every_generated_instance_satisfies_hypothesis() -> None:
    """The cardinal invariant: an adversarial search lives INSIDE the
    hypothesis domain. Every generated instance must satisfy every
    predicate in the hypothesis."""
    hyp = {"elem_ab_G_odd", "odd_weight_A", "odd_weight_B"}
    tests = generate_stress_tests(
        hypothesis_predicates=hyp,
        budget=80,
        n_max=90,
        seed=42,
    )
    assert len(tests) > 0, "generator produced no instances"
    for t in tests:
        G, A, B = _reload(t)
        assert check_all_predicates(hyp, G, A, B), (
            f"instance {t.instance_id} violates hypothesis "
            f"(axis={t.axis_probed}, value={t.value_probed})"
        )


def test_hypothesis_satisfied_metadata_matches_input() -> None:
    """Every `StressTest.hypothesis_satisfied` field records the input
    hypothesis. (Tier 3 reporting depends on this.)"""
    hyp = {"elem_ab_G_odd", "odd_weight_A"}
    tests = generate_stress_tests(
        hypothesis_predicates=hyp, budget=20, n_max=72, seed=0
    )
    assert tests
    for t in tests:
        assert set(t.hypothesis_satisfied) == hyp


# --- R1+R4 falsifier reproduction -------------------------------------------


def test_r1_r4_hypothesis_yields_mixed_rank_multi_prime() -> None:
    """The R1+R4 hypothesis leaves `prime_structure` and
    `prime_rank_profile` unpinned. The generator must produce instances
    pinning these axes — including mixed-rank multi-prime, which is
    the R1+R4 falsifier shape."""
    hyp = {"elem_ab_G_odd", "odd_weight_A", "odd_weight_B"}
    tests = generate_stress_tests(
        hypothesis_predicates=hyp, budget=200, n_max=90, seed=7
    )
    mixed_rank = [
        t
        for t in tests
        if t.axis_probed == "prime_rank_profile"
        and t.value_probed == "mixed_rank"
    ]
    assert mixed_rank, (
        "no mixed_rank instances generated despite prime_rank_profile being unpinned"
    )


def test_r1_r4_hypothesis_hits_z3_x_z15_falsifier_group() -> None:
    """Specifically, the Z_3 × Z_15 falsifier group MUST be among the
    generated mixed-rank instances. This is the exact group structure
    the round-1 R1+R4 falsifier used."""
    hyp = {"elem_ab_G_odd", "odd_weight_A", "odd_weight_B"}
    tests = generate_stress_tests(
        hypothesis_predicates=hyp, budget=400, n_max=90, seed=7
    )
    z3_x_z15 = [
        t
        for t in tests
        if t.axis_probed == "prime_rank_profile"
        and (t.ell, t.m) in {(3, 15), (15, 3)}
    ]
    assert z3_x_z15, (
        "no Z_3 × Z_15 instances generated; the R1+R4 falsifier group is missing"
    )


# --- axis coverage ----------------------------------------------------------


def test_generator_probes_only_unpinned_axes_by_default() -> None:
    """When `axes` is None (default), the generator should only produce
    instances on axes NOT pinned by the hypothesis."""
    hyp = {"elem_ab_G_odd", "odd_weight_A", "odd_weight_B"}
    unp = unpinned_axes(hyp)
    tests = generate_stress_tests(
        hypothesis_predicates=hyp, budget=120, n_max=90, seed=11
    )
    probed_axes = {t.axis_probed for t in tests}
    assert probed_axes.issubset(unp)


def test_explicit_axes_argument_constrains_generation() -> None:
    """Passing `axes=` should restrict generation to those axes only."""
    hyp = {"elem_ab_G_odd", "odd_weight_A", "odd_weight_B"}
    tests = generate_stress_tests(
        hypothesis_predicates=hyp,
        budget=60,
        n_max=90,
        seed=11,
        axes={"prime_rank_profile"},
    )
    probed_axes = {t.axis_probed for t in tests}
    assert probed_axes <= {"prime_rank_profile"}


# --- n_max and k > 0 filtering ----------------------------------------------


def test_n_max_filter_respected() -> None:
    hyp = {"odd_weight_A", "odd_weight_B"}
    n_cap = 36
    tests = generate_stress_tests(
        hypothesis_predicates=hyp, budget=100, n_max=n_cap, seed=3
    )
    for t in tests:
        assert t.n <= n_cap, f"{t.instance_id}: n={t.n} > n_max={n_cap}"


def test_every_instance_has_positive_k() -> None:
    hyp = {"odd_weight_A", "odd_weight_B"}
    tests = generate_stress_tests(
        hypothesis_predicates=hyp, budget=100, n_max=72, seed=3
    )
    for t in tests:
        assert t.k > 0, f"{t.instance_id}: k={t.k} (trivial code, should be filtered)"


# --- determinism & reproducibility ------------------------------------------


def test_same_seed_gives_same_instances() -> None:
    """Identical seeds → identical instance sequences. Required for
    reproducible Tier-3 batteries."""
    hyp = {"elem_ab_G_odd", "odd_weight_A", "odd_weight_B"}
    a = generate_stress_tests(
        hypothesis_predicates=hyp, budget=50, n_max=60, seed=99
    )
    b = generate_stress_tests(
        hypothesis_predicates=hyp, budget=50, n_max=60, seed=99
    )
    assert [t.instance_id for t in a] == [t.instance_id for t in b]


def test_different_seeds_give_different_instances() -> None:
    hyp = {"elem_ab_G_odd", "odd_weight_A", "odd_weight_B"}
    a = generate_stress_tests(
        hypothesis_predicates=hyp, budget=50, n_max=60, seed=1
    )
    b = generate_stress_tests(
        hypothesis_predicates=hyp, budget=50, n_max=60, seed=2
    )
    # Most instances should differ between seeds.
    a_ids = {t.instance_id for t in a}
    b_ids = {t.instance_id for t in b}
    assert len(a_ids & b_ids) < min(len(a_ids), len(b_ids))


# --- empty cases ------------------------------------------------------------


def test_returns_empty_list_when_no_unpinned_axes_have_templates() -> None:
    """Passing `axes=` set to a nonexistent axis returns no instances."""
    hyp = {"odd_weight_A"}
    tests = generate_stress_tests(
        hypothesis_predicates=hyp,
        budget=50,
        n_max=72,
        seed=0,
        axes={"not_a_real_axis"},
    )
    assert tests == []


# --- introspection ----------------------------------------------------------


def test_supported_axis_value_pairs_includes_round1_relevant_pairs() -> None:
    pairs = set(supported_axis_value_pairs())
    assert ("prime_structure", "multi") in pairs
    assert ("prime_structure", "single") in pairs
    assert ("prime_rank_profile", "mixed_rank") in pairs
    assert ("prime_rank_profile", "all_rank_1") in pairs
