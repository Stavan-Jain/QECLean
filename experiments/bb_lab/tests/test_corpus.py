"""Tests for the corpus read-only query interface.

Build a tiny DB with a few rows of known structure, then verify that
`Corpus` produces the right counts and shapes under each filter
combinator.
"""

from __future__ import annotations

from pathlib import Path

import pytest

from bb_lab.corpus import Corpus
from bb_lab.store import StoredInstance, connect, upsert_instance


def _seed_db(db: Path) -> None:
    """Populate `db` with a deterministic 6-row mini-corpus."""
    rows = [
        # (code_id, gstruct, ell, m, n, k, d_exact, d_ub)
        ("a", "Z3xZ3", 3, 3, 18, 4,  5,    5),
        ("b", "Z3xZ3", 3, 3, 18, 8,  7,    7),
        ("c", "Z3xZ4", 3, 4, 24, 4,  6,    6),
        ("d", "Z3xZ4", 3, 4, 24, 8,  None, 10),
        ("e", "Z3xZ6", 3, 6, 36, 12, 8,    None),
        ("f", "Z6xZ6", 6, 6, 72, 12, 10,   10),
    ]
    with connect(db) as con:
        for (cid, gs, ell, m_, n_, k_, d, dub) in rows:
            inst = StoredInstance(
                instance_id=cid, code_id=cid, group_struct=gs,
                ell=ell, m=m_, n=n_, k=k_,
                A_poly=f"poly_{cid}_A", B_poly=f"poly_{cid}_B",
                A_weight=3, B_weight=3,
                d_exact=d, d_method="test" if d is not None else None,
                d_ub=dub,
            )
            upsert_instance(con, inst)


@pytest.fixture
def mini_db(tmp_path: Path) -> Path:
    db = tmp_path / "mini.duckdb"
    _seed_db(db)
    return db


def test_count_all(mini_db):
    c = Corpus(db_path=mini_db)
    assert c.count() == 6


def test_filter_equality(mini_db):
    c = Corpus(db_path=mini_db).filter(group_struct="Z3xZ3")
    assert c.count() == 2
    ids = sorted(r["instance_id"] for r in c)
    assert ids == ["a", "b"]


def test_filter_gte_lte(mini_db):
    c = Corpus(db_path=mini_db).filter(n_lte=30, k_gte=4)
    # Rows with n ≤ 30 and k ≥ 4: a (n=18,k=4), b (n=18,k=8), c (n=24,k=4), d (n=24,k=8)
    assert c.count() == 4


def test_filter_in(mini_db):
    c = Corpus(db_path=mini_db).filter(group_struct_in=["Z3xZ6", "Z6xZ6"])
    assert c.count() == 2
    assert {r["code_id"] for r in c} == {"e", "f"}


def test_filter_in_empty(mini_db):
    c = Corpus(db_path=mini_db).filter(group_struct_in=[])
    assert c.count() == 0


def test_filter_null(mini_db):
    c = Corpus(db_path=mini_db).filter(d_exact_is_null=True)
    assert c.count() == 1
    assert next(iter(c))["code_id"] == "d"


def test_filter_not_null(mini_db):
    c = Corpus(db_path=mini_db).filter(d_ub_is_not_null=True)
    assert c.count() == 5  # everyone except 'e' has d_ub


def test_filter_chaining(mini_db):
    c = (
        Corpus(db_path=mini_db)
        .filter(d_exact_gte=6)
        .filter(d_exact_lte=8)
    )
    assert c.count() == 3  # b(d=7), c(d=6), e(d=8)


def test_order_by(mini_db):
    c = Corpus(db_path=mini_db).order_by("n", "k")
    rows = list(c)
    ns = [r["n"] for r in rows]
    assert ns == sorted(ns)


def test_limited(mini_db):
    c = Corpus(db_path=mini_db).order_by("n").limited(3)
    assert c.count() == 3


def test_column(mini_db):
    arr = Corpus(db_path=mini_db).column("n")
    assert sorted(arr) == [18, 18, 24, 24, 36, 72]


def test_columns_metadata(mini_db):
    cols = Corpus(db_path=mini_db).columns()
    assert "instance_id" in cols
    assert "d_exact" in cols
    assert "group_struct" in cols


def test_iter_yields_dicts(mini_db):
    c = Corpus(db_path=mini_db).filter(code_id="a")
    row = next(iter(c))
    assert isinstance(row, dict)
    assert row["code_id"] == "a"
    assert row["n"] == 18


def test_summary(mini_db):
    s = Corpus(db_path=mini_db).summary()
    assert s["n_rows"] == 6
    assert s["n_range"] == (18, 72)
    assert s["k_range"] == (4, 12)
    assert s["d_exact_range"] == (5, 10)
    assert s["n_with_d_exact"] == 5
    assert s["n_with_d_ub"] == 5
    assert s["n_distinct_groups"] == 4


def test_groupby_counts(mini_db):
    counts = Corpus(db_path=mini_db).groupby_counts("group_struct")
    # Z3xZ3: 2, Z3xZ4: 2, Z3xZ6: 1, Z6xZ6: 1
    counts_d = dict(counts)
    assert counts_d == {"Z3xZ3": 2, "Z3xZ4": 2, "Z3xZ6": 1, "Z6xZ6": 1}


def test_to_arrow_returns_arrow_table(mini_db):
    table = Corpus(db_path=mini_db).filter(group_struct="Z3xZ3").to_arrow()
    assert table.num_rows == 2
    # pyarrow Table behaviour
    assert "instance_id" in table.column_names


def test_db_not_found_raises(tmp_path):
    bad = tmp_path / "does-not-exist.duckdb"
    with pytest.raises(FileNotFoundError):
        Corpus(db_path=bad).count()


def test_read_only_does_not_create_db(tmp_path):
    """Opening a Corpus must not auto-create the DB."""
    bad = tmp_path / "nope.duckdb"
    with pytest.raises(FileNotFoundError):
        Corpus(db_path=bad).fetchall()
    assert not bad.exists()
