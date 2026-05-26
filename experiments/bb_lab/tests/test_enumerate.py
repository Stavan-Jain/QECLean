"""Tests for the BB enumeration pipeline."""

from __future__ import annotations

from collections import Counter

import pytest

from bb_lab.canonical import canonical_pair, is_canonical
from bb_lab.automorphism import automorphisms
from bb_lab.enumerate_bb import enumerate_canonical_pairs
from bb_lab.group import ZmZn


def test_enumerate_z3z3_w3_count():
    """Z_3 × Z_3 with weight 3 — small enough to enumerate exhaustively
    and small enough to verify by hand. We expect 19 canonical reps,
    of which 12 have k ≥ 2 (the other 7 are k=0 codes)."""
    G = ZmZn(3, 3)
    all_instances = list(enumerate_canonical_pairs(G, weight=3))
    assert len(all_instances) == 19
    nontrivial = [i for i in all_instances if i.k >= 2]
    assert len(nontrivial) == 12


def test_enumerate_yields_canonical_only():
    """Every yielded instance is the canonical orbit representative."""
    G = ZmZn(3, 4)
    auts = automorphisms(G)
    for inst in enumerate_canonical_pairs(G, weight=3):
        assert is_canonical(
            set(inst.canonical.A_support),
            set(inst.canonical.B_support),
            G, auts=auts,
        )


def test_enumerate_no_duplicates():
    """No two yielded instances are in the same orbit."""
    G = ZmZn(3, 4)
    auts = automorphisms(G)
    instances = list(enumerate_canonical_pairs(G, weight=3))
    keys = []
    for inst in instances:
        canon = canonical_pair(
            set(inst.canonical.A_support),
            set(inst.canonical.B_support),
            G, auts=auts,
        )
        keys.append((canon.A_support, canon.B_support))
    assert len(keys) == len(set(keys))


def test_enumerate_features_consistent():
    """For every yielded instance, n = 2|G| and k = n − rank H_X − rank H_Z."""
    G = ZmZn(3, 4)
    for inst in enumerate_canonical_pairs(G, weight=3, only_k_geq=0):
        assert inst.n == 2 * G.cardinality
        assert inst.k == inst.n - inst.rank_HX - inst.rank_HZ
        # CSS BB symmetry: rank(H_X) == rank(H_Z) for any BB code.
        assert inst.rank_HX == inst.rank_HZ
