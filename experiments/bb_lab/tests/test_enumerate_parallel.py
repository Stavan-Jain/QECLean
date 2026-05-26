"""Parallel `enumerate_canonical_pairs_parallel` should produce the
same orbit set as the serial `enumerate_canonical_pairs`, modulo order.

We assert set-equality on the canonical (A_support, B_support) pairs
so the test is robust to non-deterministic worker scheduling.
"""

from __future__ import annotations

import pytest

from bb_lab.enumerate_bb import (
    enumerate_canonical_pairs,
    enumerate_canonical_pairs_parallel,
)
from bb_lab.group import ZmZn


def _orbit_keys(instances) -> set:
    return {
        (inst.canonical.A_support, inst.canonical.B_support)
        for inst in instances
    }


@pytest.mark.parametrize("ell,m,weight,n_workers", [
    (3, 3, 3, 1),   # degenerate parallel path
    (3, 3, 3, 2),
    (3, 3, 3, 4),
    (3, 4, 3, 2),
    (3, 4, 3, 4),
])
def test_parallel_matches_serial(ell, m, weight, n_workers):
    G = ZmZn(ell, m)
    serial = list(enumerate_canonical_pairs(G, weight=weight))
    parallel = enumerate_canonical_pairs_parallel(
        G, weight=weight, n_workers=n_workers,
    )
    assert _orbit_keys(serial) == _orbit_keys(parallel), (
        f"parallel-{n_workers} on Z_{ell}xZ_{m} differs from serial: "
        f"serial extras={_orbit_keys(serial) - _orbit_keys(parallel)}, "
        f"parallel extras={_orbit_keys(parallel) - _orbit_keys(serial)}"
    )
    assert len(serial) == len(parallel), (
        f"orbit set matches but cardinality differs (duplicates?): "
        f"serial={len(serial)}, parallel={len(parallel)}"
    )


def test_parallel_preserves_only_k_geq(tmp_path):
    """only_k_geq filter applies inside workers, before pickling."""
    G = ZmZn(3, 4)
    all_inst = enumerate_canonical_pairs_parallel(
        G, weight=3, n_workers=4,
    )
    filtered = enumerate_canonical_pairs_parallel(
        G, weight=3, only_k_geq=4, n_workers=4,
    )
    # Filtered ⊆ all, and every filtered instance has k ≥ 4.
    assert _orbit_keys(filtered).issubset(_orbit_keys(all_inst))
    assert all(inst.k >= 4 for inst in filtered)
    # And the cut is exactly the rows below the threshold.
    cut_count = sum(1 for inst in all_inst if inst.k >= 4)
    assert len(filtered) == cut_count


def test_parallel_per_instance_features_match_serial():
    """For each orbit returned by both, EnumeratedInstance fields
    (n, k, rank_HX, dim_ker_A, ...) agree. This catches a class of bug
    where the parallel path corrupts the `EnumeratedInstance` via
    incomplete pickling or stale workers."""
    G = ZmZn(3, 4)
    serial = {
        (inst.canonical.A_support, inst.canonical.B_support): inst
        for inst in enumerate_canonical_pairs(G, weight=3)
    }
    parallel = {
        (inst.canonical.A_support, inst.canonical.B_support): inst
        for inst in enumerate_canonical_pairs_parallel(
            G, weight=3, n_workers=4,
        )
    }
    assert set(serial) == set(parallel)
    for key, s_inst in serial.items():
        p_inst = parallel[key]
        assert (s_inst.n, s_inst.k) == (p_inst.n, p_inst.k)
        assert (s_inst.A_weight, s_inst.B_weight) == (p_inst.A_weight, p_inst.B_weight)
        assert (s_inst.rank_HX, s_inst.rank_HZ) == (p_inst.rank_HX, p_inst.rank_HZ)
        assert (s_inst.dim_ker_A, s_inst.dim_ker_B) == (p_inst.dim_ker_A, p_inst.dim_ker_B)
        assert s_inst.canonical.orbit_size == p_inst.canonical.orbit_size
