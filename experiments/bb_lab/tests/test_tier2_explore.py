"""Smoke + integration tests for the Tier-2 first-conjecture-mill script.

The script is `experiments/bb_lab/scripts/tier2_explore.py`. We import
its `evaluate_candidate` / `render_report` helpers and exercise them on
a tiny tmp-dir DB seeded by hand. This keeps the script under CI even
though it's outside the `src/` package.
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

import pytest

from bb_lab.corpus import Corpus
from bb_lab.store import connect


SCRIPT = (
    Path(__file__).resolve().parent.parent / "scripts" / "tier2_explore.py"
)


def _load_script_module():
    spec = importlib.util.spec_from_file_location("tier2_explore", SCRIPT)
    mod = importlib.util.module_from_spec(spec)
    sys.modules["tier2_explore"] = mod
    spec.loader.exec_module(mod)
    return mod


def _seed_db(db: Path) -> None:
    """Mini corpus where the textbook bound holds correctly
    (`d_exact ≤ min(min_wt_ker_A, min_wt_ker_B)`)."""
    with connect(db) as con:
        for col in ("tanner_girth", "supp_diameter_A", "supp_diameter_B",
                    "min_wt_ker_A", "min_wt_ker_B"):
            try:
                con.execute(f"ALTER TABLE bb_instances ADD COLUMN {col} INTEGER")
            except Exception:
                pass
        # Realistic-ish row where d ≤ min(mw_ker_A, mw_ker_B):
        #   d = 5,  mw_A = 6,  mw_B = 7   → bound = 6, looseness = 1
        # And one where the bound is tight:
        #   d = 4,  mw_A = 4,  mw_B = 6   → bound = 4, looseness = 0
        rows = [
            # (cid, gs, ell, m, n, k, d, A_w, B_w, dim_A, dim_B, tg, sd_A, sd_B, mw_A, mw_B)
            ("a", "Z3xZ3", 3, 3, 18, 4, 5, 3, 3, 4, 4, 4, 2, 2, 6, 7),  # loose
            ("b", "Z3xZ3", 3, 3, 18, 4, 4, 3, 3, 4, 4, 4, 2, 2, 4, 6),  # tight
            ("c", "Z3xZ4", 3, 4, 24, 8, 6, 3, 3, 4, 4, 4, 2, 3, 6, 6),  # tight
        ]
        for (cid, gs, ell, m_, n_, k_, d, A_w, B_w,
             dim_A, dim_B, tg, sd_A, sd_B, mw_A, mw_B) in rows:
            con.execute(
                "INSERT INTO bb_instances (instance_id, code_id, group_struct, "
                "ell, m, n, k, A_poly, B_poly, A_weight, B_weight, "
                "dim_ker_A, dim_ker_B, tanner_girth, supp_diameter_A, "
                "supp_diameter_B, min_wt_ker_A, min_wt_ker_B, d_exact, "
                "d_method, inserted_at, updated_at) "
                "VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,'hand',now(),now())",
                [cid, cid, gs, ell, m_, n_, k_, f"p{cid}A", f"p{cid}B",
                 A_w, B_w, dim_A, dim_B, tg, sd_A, sd_B, mw_A, mw_B, d],
            )


@pytest.fixture
def mini_corpus_db(tmp_path: Path) -> Path:
    db = tmp_path / "mini.duckdb"
    _seed_db(db)
    return db


def test_evaluate_css_classical_dual(mini_corpus_db):
    """The published CSS dual bound should never be violated by a
    correct corpus (looseness ≥ 0 for every row)."""
    mod = _load_script_module()
    cand = next(c for c in mod.CANDIDATES if c.name == "CSS_classical_dual")
    corpus = Corpus(db_path=mini_corpus_db)
    report = mod.evaluate_candidate(corpus, cand, group_filter=None)
    assert report["applicable_rows"] == 3
    assert not report["violations"], (
        f"CSS dual bound shouldn't be violated by valid corpus rows; "
        f"got {report['violations']}"
    )
    assert report["min_looseness"] >= 0
    # Per the seed values, tight cases: b (d=4, bound=4), c (d=6, bound=6).
    assert report["tight_count"] == 2


def test_evaluate_with_group_filter(mini_corpus_db):
    mod = _load_script_module()
    cand = next(c for c in mod.CANDIDATES if c.name == "CSS_classical_dual")
    corpus = Corpus(db_path=mini_corpus_db)
    report = mod.evaluate_candidate(corpus, cand, group_filter=["Z3xZ4"])
    assert report["applicable_rows"] == 1
    assert "Z3xZ4" in report["per_group_tight"]


def test_evaluate_handles_missing_columns(tmp_path):
    """A DB without min_wt_ker_A populated produces a 0-applicable report."""
    mod = _load_script_module()
    db = tmp_path / "no_features.duckdb"
    with connect(db) as con:
        # Don't ALTER any feature columns. d_exact is set.
        con.execute(
            "INSERT INTO bb_instances (instance_id, code_id, group_struct, "
            "ell, m, n, k, A_poly, B_poly, A_weight, B_weight, "
            "d_exact, d_method, inserted_at, updated_at) "
            "VALUES (?,?,?,?,?,?,?,?,?,?,?,?, 'hand', now(), now())",
            ["x", "x", "Z3xZ3", 3, 3, 18, 4, "A", "B", 3, 3, 6],
        )
    corpus = Corpus(db_path=db)
    cand = next(c for c in mod.CANDIDATES if c.name == "CSS_classical_dual")
    report = mod.evaluate_candidate(corpus, cand, group_filter=None)
    assert report["applicable_rows"] == 0


def test_render_report_returns_string(mini_corpus_db):
    mod = _load_script_module()
    corpus = Corpus(db_path=mini_corpus_db)
    reports = [
        mod.evaluate_candidate(corpus, c, group_filter=None)
        for c in mod.CANDIDATES
    ]
    text = mod.render_report(reports)
    assert "CSS_classical_dual" in text
    assert "tight examples" in text or "loose examples" in text
