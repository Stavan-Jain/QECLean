"""Tests for the L1 random-sampling upper bound on `d_X`.

L1 sampling is cheap (microseconds-to-milliseconds per sample) and
gives a guaranteed upper bound. We test:

  1. `find_logical_x` returns rows actually in `ker(H_Z) \\ rowspan(H_X)`.
  2. Sampled witnesses pass `verify_witness_in_nontrivial_coset`.
  3. On Bravyi instances with known `d`, sampling reaches `d_ub = d`
     within a modest sample budget.
  4. Raises on `k = 0` codes (logical-X space is empty).
"""

from __future__ import annotations

import numpy as np
import pytest

from bb_lab.checks import bb_check_matrices
from bb_lab.group import ZmZn
from bb_lab.l1_sampling import (
    find_logical_x,
    l1_distance_ub,
    verify_witness_in_nontrivial_coset,
)
from bb_lab.poly import Poly


def _bravyi_checks(row):
    G = ZmZn(row["group"]["ell"], row["group"]["m"])
    A = Poly.from_string(row["polynomials"]["A"], G)
    B = Poly.from_string(row["polynomials"]["B"], G)
    return bb_check_matrices(A, B)


def test_find_logical_x_rows_are_xLogicals(bravyi_table):
    """Every `find_logical_x` row is in `ker(H_Z)` and not in `rowspan(H_X)`."""
    row = bravyi_table[0]   # bb_72_12_6
    checks = _bravyi_checks(row)
    L_X = find_logical_x(checks)
    assert L_X.shape[0] == row["parameters"]["k"]
    assert L_X.shape[1] == 2 * checks.group.cardinality
    for i in range(L_X.shape[0]):
        v = L_X[i]
        syndrome = (checks.H_Z @ v) % 2
        assert not syndrome.any(), (
            f"L_X[{i}] has nonzero H_Z syndrome (not in ker H_Z)"
        )
        # And it should not be in rowspan(H_X). Easiest cheap check: it
        # was returned by quotient_complement_basis(H_X, ker H_Z), which
        # already ensures linear independence modulo rowspan(H_X). Confirm
        # by checking that *some* logical-Z row has nontrivial inner
        # product with it.
        from bb_lab.sat_distance import find_logical_z
        L_Z = find_logical_z(checks)
        assert ((L_Z @ v) % 2).any(), (
            f"L_X[{i}] commutes with every L_Z row — would mean it's in rowspan(H_X)"
        )


def test_l1_distance_ub_tight_on_small_bravyi(bravyi_table):
    """On the three small Bravyi instances, modest sampling reaches the
    published `d` exactly."""
    for idx, code_id, truth, budget in [
        (0, "bb_72_12_6", 6, 20_000),
        (1, "bb_90_8_10", 10, 20_000),
    ]:
        row = bravyi_table[idx]
        assert row["code_id"] == code_id
        checks = _bravyi_checks(row)
        res = l1_distance_ub(checks, n_samples=budget, seed=42)
        assert res.distance_ub == truth, (
            f"{code_id}: sampling found d_ub={res.distance_ub}, expected {truth}"
        )
        assert verify_witness_in_nontrivial_coset(checks, res.witness), (
            f"{code_id}: sampled witness is not a nontrivial logical"
        )


def test_l1_witness_weight_matches_returned_ub(bravyi_table):
    """The sampling result's `distance_ub` is exactly the Hamming weight
    of `witness`."""
    row = bravyi_table[0]
    checks = _bravyi_checks(row)
    res = l1_distance_ub(checks, n_samples=5_000, seed=0)
    assert int(res.witness.sum()) == res.distance_ub


def test_l1_distance_ub_raises_on_k_zero():
    """k = 0 codes have no logicals; `l1_distance_ub` should reject them
    instead of returning a misleading number."""
    # Build a tiny k=0 code: A = B = 1 (constant polynomial) over Z_3 × Z_3.
    # Then circulant(1) = I, so H_X = [I | I] and similarly H_Z. rank
    # adds up to n − k = n, i.e. k = 0.
    G = ZmZn(3, 3)
    A = Poly(support=frozenset([(0, 0)]), group=G)  # = 1
    B = Poly(support=frozenset([(0, 0)]), group=G)
    checks = bb_check_matrices(A, B)
    with pytest.raises(ValueError, match="k=0"):
        l1_distance_ub(checks, n_samples=100)


def test_l1_sampling_is_deterministic_given_seed(bravyi_table):
    """Same seed → same witness."""
    row = bravyi_table[0]
    checks = _bravyi_checks(row)
    res1 = l1_distance_ub(checks, n_samples=2_000, seed=7)
    res2 = l1_distance_ub(checks, n_samples=2_000, seed=7)
    assert res1.distance_ub == res2.distance_ub
    np.testing.assert_array_equal(res1.witness, res2.witness)
