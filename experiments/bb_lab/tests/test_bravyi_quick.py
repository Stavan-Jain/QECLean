"""Verify (n, k) of every Bravyi instance — the cheap half of the v0 gate."""

from __future__ import annotations

import pytest

from bb_lab.checks import assert_css_commutation, bb_check_matrices
from bb_lab.codeparams import code_params
from bb_lab.group import ZmZn
from bb_lab.poly import Poly


def test_bravyi_table_has_five_entries(bravyi_table):
    assert len(bravyi_table) == 5
    code_ids = {row["code_id"] for row in bravyi_table}
    assert code_ids == {
        "bb_72_12_6", "bb_90_8_10", "bb_108_8_10",
        "gross", "bb_288_12_18",
    }


@pytest.mark.parametrize("idx", [0, 1, 2, 3, 4])
def test_nk_matches_published(bravyi_table, idx):
    row = bravyi_table[idx]
    G = ZmZn(row["group"]["ell"], row["group"]["m"])
    A = Poly.from_string(row["polynomials"]["A"], G)
    B = Poly.from_string(row["polynomials"]["B"], G)
    C = bb_check_matrices(A, B)
    assert_css_commutation(C)
    p = code_params(C)
    expected = row["parameters"]
    assert p.n == expected["n"], (
        f"{row['code_id']}: n = {p.n}, expected {expected['n']}"
    )
    assert p.k == expected["k"], (
        f"{row['code_id']}: k = {p.k}, expected {expected['k']}"
    )
    # BB codes have rank(H_X) = rank(H_Z) by symmetry.
    assert p.rank_HX == p.rank_HZ, (
        f"{row['code_id']}: rank(H_X)={p.rank_HX} != rank(H_Z)={p.rank_HZ}"
    )
