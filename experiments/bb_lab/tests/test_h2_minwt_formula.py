"""Tests for the (4/9)|G| H_2 min-weight formula on weight-3 BB codes."""

from __future__ import annotations

from pathlib import Path

import numpy as np
import pytest
import yaml

from bb_lab.checks import circulant
from bb_lab.group import ZmZn
from bb_lab.h2_minwt_formula import (
    closed_form_formula,
    construct_h2_witness,
    find_refined_z3_pair,
    min_wt_h2_upper_bound,
)
from bb_lab.linalg import nullspace_f2
from bb_lab.poly import Poly


@pytest.fixture(scope="module")
def bravyi_instances():
    """Load the 5 Bravyi-table instances."""
    repo = Path(__file__).resolve().parents[1]
    table_path = repo / "instances" / "bravyi_table.yaml"
    with open(table_path) as f:
        data = yaml.safe_load(f)
    return data["instances"]


def _min_wt_brute(M_A, M_B):
    basis = nullspace_f2(np.concatenate([M_A, M_B], axis=0))
    dim = basis.shape[0]
    if dim == 0:
        return 0
    n = basis.shape[1]
    best = n + 1
    for mask in range(1, 1 << dim):
        v = np.zeros(n, dtype=np.uint8)
        for i in range(dim):
            if (mask >> i) & 1:
                v ^= basis[i]
        w = int(v.sum())
        if 0 < w < best:
            best = w
    return best


# -----------------------------------------------------------------------------
# Bravyi-table tests: all 5 instances should hit (4/9)|G| exactly.
# -----------------------------------------------------------------------------


@pytest.mark.parametrize("code_id,expected_min_wt", [
    ("bb_72_12_6", 16),    # (4/9)*36 = 16
    ("bb_90_8_10", 20),     # (4/9)*45 = 20
    ("bb_108_8_10", 24),    # (4/9)*54 = 24
    ("gross", 32),          # (4/9)*72 = 32
    ("bb_288_12_18", 64),   # (4/9)*144 = 64
])
def test_bravyi_instance_formula(
    bravyi_instances, code_id, expected_min_wt
):
    """Each Bravyi instance must (a) have a refined pair, (b) constructed
    witness has weight (4/9)|G|, (c) actual brute-force min_wt matches."""
    inst = next(i for i in bravyi_instances if i["code_id"] == code_id)
    G = ZmZn(inst["group"]["ell"], inst["group"]["m"])
    A = Poly.from_string(inst["polynomials"]["A"], G)
    B = Poly.from_string(inst["polynomials"]["B"], G)

    pair = find_refined_z3_pair(A, B)
    assert pair is not None, f"{code_id}: refined Z_3 pair should exist"

    bound = min_wt_h2_upper_bound(A, B, G)
    assert bound == expected_min_wt, (
        f"{code_id}: upper bound {bound} != expected {expected_min_wt}"
    )

    witness = construct_h2_witness(A, B, G)
    assert witness is not None
    assert int(witness.sum()) == expected_min_wt

    # Verify witness is in Ann(A) ∩ Ann(B)
    M_A = circulant(A)
    M_B = circulant(B)
    assert int(((M_A @ witness) % 2).sum()) == 0, (
        f"{code_id}: witness not in Ann(A)"
    )
    assert int(((M_B @ witness) % 2).sum()) == 0, (
        f"{code_id}: witness not in Ann(B)"
    )

    # Actual min_wt(H_2) should be ≤ bound; for Bravyi instances it's tight
    actual_min = _min_wt_brute(M_A, M_B)
    assert actual_min == expected_min_wt, (
        f"{code_id}: actual min_wt {actual_min} != expected {expected_min_wt}"
    )


# -----------------------------------------------------------------------------
# Refined pair conditions
# -----------------------------------------------------------------------------


def test_refined_pair_canonical_gross():
    """Gross's canonical refined pair: phi_A = y mod 3, phi_B = x mod 3."""
    G = ZmZn(12, 6)
    A = Poly.from_string("x^3 + y + y^2", G)
    B = Poly.from_string("y^3 + x + x^2", G)
    pair = find_refined_z3_pair(A, B)
    assert pair is not None
    (a1, b1), (a2, b2) = pair
    # First found pair (canonical order): phi_A=(0,1), phi_B=(1,0)
    # i.e., phi_A(x,y)=y mod 3, phi_B(x,y)=x mod 3
    assert (a1, b1) == (0, 1), f"Expected (0,1), got ({a1},{b1})"
    assert (a2, b2) == (1, 0), f"Expected (1,0), got ({a2},{b2})"


def test_no_refined_pair_z3xz4():
    """Z_3 x Z_4: only 3 | ell, not m. No refined pair should exist."""
    G = ZmZn(3, 4)
    A = Poly.from_string("y + x + x^2", G)
    B = Poly.from_string("1 + x*y^2 + x^2*y^2", G)
    pair = find_refined_z3_pair(A, B)
    assert pair is None
    assert min_wt_h2_upper_bound(A, B, G) is None
    assert construct_h2_witness(A, B, G) is None


def test_no_refined_pair_constants_only():
    """A and B both only y-dependent: refined pair shouldn't find indep."""
    G = ZmZn(6, 6)
    A = Poly.from_string("1 + y + y^2", G)
    B = Poly.from_string("1 + y + y^2", G)
    pair = find_refined_z3_pair(A, B)
    # phi_A = y mod 3 works for A. phi_B = y mod 3 works for B. Same hom.
    # No two LINEARLY INDEPENDENT homs.
    assert pair is None


# -----------------------------------------------------------------------------
# Witness construction correctness
# -----------------------------------------------------------------------------


def test_witness_weight_is_four_ninths():
    """Witness weight equals (4/9)|G| exactly."""
    G = ZmZn(12, 6)  # gross group
    A = Poly.from_string("x^3 + y + y^2", G)
    B = Poly.from_string("y^3 + x + x^2", G)
    witness = construct_h2_witness(A, B, G)
    assert witness is not None
    assert int(witness.sum()) == 32
    assert int(witness.sum()) * 9 == 4 * G.cardinality


def test_witness_is_in_ann_A_and_ann_B():
    """Witness must lie in the joint kernel Ann(A) ∩ Ann(B)."""
    G = ZmZn(15, 6)  # bb_90 group? no, (15, 3). use Z_15xZ_6
    # Use a Bravyi-like example
    A = Poly.from_string("y + y^2 + x^9", G)
    B = Poly.from_string("y^3 + x + x^2", G)
    witness = construct_h2_witness(A, B, G)
    if witness is None:
        pytest.skip("No refined pair for this instance")
    M_A = circulant(A)
    M_B = circulant(B)
    assert int(((M_A @ witness) % 2).sum()) == 0
    assert int(((M_B @ witness) % 2).sum()) == 0


# -----------------------------------------------------------------------------
# Closed-form formula
# -----------------------------------------------------------------------------


def test_closed_form_weight_3():
    """For weight-3 polynomials, formula gives (4/9)·|G|."""
    assert abs(closed_form_formula(3, 72) - 32) < 1e-9
    assert abs(closed_form_formula(3, 36) - 16) < 1e-9
    assert abs(closed_form_formula(3, 144) - 64) < 1e-9


def test_closed_form_weight_4():
    """For weight-4 polynomials, formula gives (9/16)·|G|."""
    assert abs(closed_form_formula(4, 144) - 81) < 1e-9


def test_closed_form_invalid_weight():
    """Weight 0 returns 0."""
    assert closed_form_formula(0, 100) == 0.0


# -----------------------------------------------------------------------------
# Theorem holds across a sample of the corpus
# -----------------------------------------------------------------------------


def test_corpus_sample_construction_validity():
    """For a sample of corpus instances with refined pair, the constructed
    element must be in H_2 with weight (4/9)|G|."""
    repo = Path(__file__).resolve().parents[1]
    db_path = repo / "data" / "bb_instances.duckdb"
    if not db_path.exists():
        pytest.skip("Corpus DB not available")

    import duckdb
    con = duckdb.connect(str(db_path), read_only=True)
    rows = con.execute(
        """SELECT instance_id, ell, m, A_poly, B_poly
           FROM bb_instances
           WHERE d_exact IS NOT NULL
             AND (ell % 3 = 0) AND (m % 3 = 0)
           ORDER BY ell*m, instance_id
           LIMIT 50"""
    ).fetchall()

    constructions_verified = 0
    for instance_id, ell, m, A_str, B_str in rows:
        G = ZmZn(ell, m)
        A = Poly.from_string(A_str, G)
        B = Poly.from_string(B_str, G)
        witness = construct_h2_witness(A, B, G)
        if witness is None:
            continue
        M_A = circulant(A)
        M_B = circulant(B)
        assert int(((M_A @ witness) % 2).sum()) == 0, (
            f"{instance_id}: witness not in Ann(A)"
        )
        assert int(((M_B @ witness) % 2).sum()) == 0, (
            f"{instance_id}: witness not in Ann(B)"
        )
        n = G.cardinality
        expected_wt = (4 * n) // 9
        assert int(witness.sum()) == expected_wt, (
            f"{instance_id}: weight {int(witness.sum())} != "
            f"expected (4/9)|G| = {expected_wt}"
        )
        constructions_verified += 1
    # Bravyi-aligned subset gives ~30 cases in first 50 rows; at least 1 should match
    assert constructions_verified >= 1
