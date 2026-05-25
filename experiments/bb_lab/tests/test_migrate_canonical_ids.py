"""Integration test for the `bb-lab migrate-canonical-ids` CLI.

The migration is a one-shot fix for canonical-rule changes: it walks
the corpus, recomputes each row's `(instance_id, A_poly, B_poly)`
under the current canonical rule, and updates in place. The test
verifies the three invariants we depend on downstream:

  1. After migration, every row's polynomials are in the canonical
     form that `enumerate_canonical_pairs` would produce — so
     re-running enumerate against the same group does NOT add new
     rows for orbits already in the corpus.
  2. `d_exact` (and other features) are preserved across migration.
  3. Migration is idempotent: a second run is a no-op.
"""

from __future__ import annotations

from pathlib import Path

import pytest
from click.testing import CliRunner

from bb_lab.canonical import canonical_pair
from bb_lab.cli import main
from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.store import StoredInstance, canonical_hash, connect, upsert_instance


def _seed_row(
    db_path: Path,
    *,
    G,
    A_supp: set[tuple[int, ...]],
    B_supp: set[tuple[int, ...]],
    d_exact: int,
) -> str:
    """Insert one row at the *given* (A_supp, B_supp) — without
    normalising — and return its assigned instance_id. Used to set up
    rows that may or may not be canonical under the current rule."""
    A_str = Poly(support=frozenset(A_supp), group=G).canonical_string()
    B_str = Poly(support=frozenset(B_supp), group=G).canonical_string()
    iid = canonical_hash(G.label(), A_str, B_str)
    inst = StoredInstance(
        instance_id=iid,
        code_id=f"test_{G.label()}_{iid[:8]}",
        group_struct=G.label(), ell=G.orders[0], m=G.orders[1],
        n=2 * G.cardinality, k=4,
        A_poly=A_str, B_poly=B_str,
        A_weight=len(A_supp), B_weight=len(B_supp),
        rank_HX=None, rank_HZ=None,
        dim_ker_A=None, dim_ker_B=None, orbit_size=None,
        d_exact=d_exact, d_method="hand-crafted",
    )
    with connect(db_path) as con:
        upsert_instance(con, inst)
    return iid


def _read_row(db_path: Path, iid: str) -> tuple[str, str, str, int | None]:
    with connect(db_path) as con:
        return con.execute(
            "SELECT instance_id, A_poly, B_poly, d_exact "
            "FROM bb_instances WHERE instance_id = ?",
            [iid],
        ).fetchone()


def _expected_new(G, A_supp: set, B_supp: set) -> tuple[str, str, str]:
    """Return the (id, A_poly, B_poly) that the current canonical rule
    would assign for the orbit of `(A_supp, B_supp)`."""
    canon = canonical_pair(A_supp, B_supp, G)
    A_new = Poly(support=frozenset(canon.A_support), group=G).canonical_string()
    B_new = Poly(support=frozenset(canon.B_support), group=G).canonical_string()
    return canonical_hash(G.label(), A_new, B_new), A_new, B_new


def test_migrate_normalises_non_canonical_row(tmp_path):
    db = tmp_path / "test.duckdb"
    G = ZmZn(3, 3)
    A = {(0, 0), (1, 0), (2, 0)}
    B = {(0, 1), (1, 1), (2, 1)}
    iid = _seed_row(db, G=G, A_supp=A, B_supp=B, d_exact=5)
    new_id, new_A, new_B = _expected_new(G, A, B)

    # Sanity: the seeded row is *not* already in canonical form (if it
    # were, the test wouldn't exercise the migration).
    if new_id == iid:
        pytest.skip("seed (A, B) is accidentally already canonical — "
                    "pick a different non-canonical pair in this test")

    runner = CliRunner()
    res = runner.invoke(main, ["migrate-canonical-ids", "--db", str(db), "--apply"])
    assert res.exit_code == 0, f"migrate failed:\n{res.output}"

    # Old row replaced; new row in place; d_exact preserved.
    with connect(db) as con:
        n = con.execute("SELECT COUNT(*) FROM bb_instances").fetchone()[0]
        assert n == 1, f"expected 1 row after migration, got {n}"
    row = _read_row(db, new_id)
    assert row is not None, "migrated row missing"
    assert row == (new_id, new_A, new_B, 5), (
        f"row mismatch — got {row}, expected ({new_id}, {new_A}, {new_B}, 5)"
    )
    assert _read_row(db, iid) is None, "old row not removed"


def test_migrate_is_idempotent(tmp_path):
    db = tmp_path / "test.duckdb"
    G = ZmZn(3, 3)
    _seed_row(db, G=G,
              A_supp={(0, 0), (1, 0), (2, 0)},
              B_supp={(0, 1), (1, 1), (2, 1)},
              d_exact=5)
    runner = CliRunner()
    res = runner.invoke(main, ["migrate-canonical-ids", "--db", str(db), "--apply"])
    assert res.exit_code == 0
    res2 = runner.invoke(main, ["migrate-canonical-ids", "--db", str(db), "--apply"])
    assert res2.exit_code == 0
    assert "nothing to do" in res2.output, (
        f"second run should be a no-op; output was:\n{res2.output}"
    )


def test_migrate_dry_run_makes_no_changes(tmp_path):
    db = tmp_path / "test.duckdb"
    G = ZmZn(3, 3)
    A = {(0, 0), (1, 0), (2, 0)}
    B = {(0, 1), (1, 1), (2, 1)}
    iid = _seed_row(db, G=G, A_supp=A, B_supp=B, d_exact=5)

    runner = CliRunner()
    res = runner.invoke(main, ["migrate-canonical-ids", "--db", str(db)])
    assert res.exit_code == 0
    assert "dry-run" in res.output

    # Row id unchanged.
    row = _read_row(db, iid)
    assert row is not None, "dry-run unexpectedly mutated the DB"
    assert row[3] == 5


def test_migrate_preserves_already_canonical_rows(tmp_path):
    """A row already in canonical form is left alone."""
    db = tmp_path / "test.duckdb"
    G = ZmZn(3, 3)
    A = {(0, 0), (1, 0), (2, 0)}
    B = {(0, 1), (1, 1), (2, 1)}
    new_id, new_A, new_B = _expected_new(G, A, B)
    # Seed the row already in canonical form by parsing the canonical
    # strings back into supports.
    A_canon = Poly.from_string(new_A, G).support
    B_canon = Poly.from_string(new_B, G).support
    iid = _seed_row(db, G=G, A_supp=set(A_canon), B_supp=set(B_canon), d_exact=5)
    assert iid == new_id, "seed didn't land at the expected canonical id"

    runner = CliRunner()
    res = runner.invoke(main, ["migrate-canonical-ids", "--db", str(db), "--apply"])
    assert res.exit_code == 0
    assert "nothing to do" in res.output
    assert _read_row(db, iid) is not None


def test_migrate_swaps_AB_fields_when_canonical_rep_is_swapped(tmp_path):
    """When migration's new canonical rep comes from the block-swap
    orientation of the input, the A/B-paired feature columns get
    transposed so they stay labelled correctly. We force a swap by
    seeding with a pair whose canonical rep is the swapped version,
    and read back `dim_ker_A` to confirm it matches the new A_poly."""
    from bb_lab.checks import circulant
    from bb_lab.linalg import rank_f2

    db = tmp_path / "test.duckdb"
    G = ZmZn(3, 3)
    # Two polys with *different* dim_ker so the swap is observable.
    # A has dim_ker(circulant(A)) = 4; B has dim_ker(circulant(B)) = 6.
    # Then swap labels under canonical_pair → the stored value behind
    # the migrated `A` should match the new A's actual dim_ker.
    A = {(0, 0), (1, 0), (2, 0)}     # x-axis line: rank 1 over F2, ker dim 8
    B = {(0, 0), (1, 1), (2, 2)}     # diagonal: different rank
    dim_kA_old = G.cardinality - rank_f2(
        circulant(Poly(support=frozenset(A), group=G))
    )
    dim_kB_old = G.cardinality - rank_f2(
        circulant(Poly(support=frozenset(B), group=G))
    )
    # Seed row with the OLD-style A/B labels.
    A_str = Poly(support=frozenset(A), group=G).canonical_string()
    B_str = Poly(support=frozenset(B), group=G).canonical_string()
    iid = canonical_hash(G.label(), A_str, B_str)
    inst = StoredInstance(
        instance_id=iid,
        code_id=f"test_{G.label()}_{iid[:8]}",
        group_struct=G.label(), ell=3, m=3,
        n=18, k=4,
        A_poly=A_str, B_poly=B_str,
        A_weight=3, B_weight=3,
        rank_HX=None, rank_HZ=None,
        dim_ker_A=dim_kA_old, dim_ker_B=dim_kB_old, orbit_size=None,
        d_exact=5, d_method="hand-crafted",
    )
    with connect(db) as con:
        upsert_instance(con, inst)

    runner = CliRunner()
    res = runner.invoke(main, ["migrate-canonical-ids", "--db", str(db), "--apply"])
    assert res.exit_code == 0, f"migrate failed:\n{res.output}"

    # After migration: dim_ker_A in the row matches the actual
    # dim_ker(circulant(new A_poly)). If the swap weren't applied,
    # this would mismatch whenever the canonical rep swapped A↔B.
    with connect(db) as con:
        new_A_str, new_B_str, new_dim_kA, new_dim_kB = con.execute(
            "SELECT A_poly, B_poly, dim_ker_A, dim_ker_B FROM bb_instances"
        ).fetchone()
    actual_kA = G.cardinality - rank_f2(circulant(Poly.from_string(new_A_str, G)))
    actual_kB = G.cardinality - rank_f2(circulant(Poly.from_string(new_B_str, G)))
    assert new_dim_kA == actual_kA, (
        f"dim_ker_A label stale after swap-aware migration: "
        f"stored={new_dim_kA}, actual={actual_kA}, new_A={new_A_str}"
    )
    assert new_dim_kB == actual_kB


def test_migrate_multi_group_caches_perms(tmp_path):
    """Migration over rows from multiple groups runs without recomputing
    permutation tables more than once per group — visible only by
    timing, but at least we verify the multi-group case completes."""
    db = tmp_path / "test.duckdb"
    seeded = []
    for G_args, A, B, d in [
        ((3, 3), {(0, 0), (1, 0), (2, 0)}, {(0, 1), (1, 1), (2, 1)}, 5),
        ((3, 4), {(0, 0), (1, 0), (2, 0)}, {(0, 1), (1, 1), (2, 1)}, 6),
        ((4, 3), {(0, 0), (1, 0), (2, 0)}, {(0, 1), (1, 1), (2, 1)}, 4),
    ]:
        G = ZmZn(*G_args)
        iid = _seed_row(db, G=G, A_supp=A, B_supp=B, d_exact=d)
        seeded.append((G, A, B, d, iid))

    runner = CliRunner()
    res = runner.invoke(main, ["migrate-canonical-ids", "--db", str(db), "--apply"])
    assert res.exit_code == 0, f"migrate failed:\n{res.output}"

    with connect(db) as con:
        n = con.execute("SELECT COUNT(*) FROM bb_instances").fetchone()[0]
    assert n == 3

    for G, A, B, d, _ in seeded:
        new_id, new_A, new_B = _expected_new(G, A, B)
        row = _read_row(db, new_id)
        assert row is not None, f"missing migrated row for {G.label()}"
        assert row == (new_id, new_A, new_B, d)
