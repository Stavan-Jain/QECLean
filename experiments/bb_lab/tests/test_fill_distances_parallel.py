"""Tests for the parallel `--workers N` path of `bb-lab fill-distances`.

The parallel runner is a watchdog over per-task subprocesses:
  - up to N concurrent slots, each one its own `Pool(processes=1)`,
  - on success → record d_exact + d_method,
  - on timeout (now − t_start > timeout) → Pool.terminate() and record
    d_method = 'sat-timeout@Ns'.

Each test seeds a small DuckDB with rows referring to the 3 small
Bravyi instances (whose SAT is fast and known) plus, for the timeout
test, a forced too-tight `--timeout-per-instance`.
"""

from __future__ import annotations

from pathlib import Path

import pytest
import yaml
from click.testing import CliRunner

from bb_lab.cli import main
from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.store import StoredInstance, canonical_hash, connect, upsert_instance


LAB_ROOT = Path(__file__).resolve().parent.parent
BRAVYI = yaml.safe_load(
    (LAB_ROOT / "instances" / "bravyi_table.yaml").read_text()
)["instances"]


def _seed_pending_bravyi(db: Path, code_ids: list[str]) -> dict[str, int]:
    """Insert the named Bravyi rows with `d_exact=NULL`. Return a
    {code_id → known d} map for assertions."""
    truth: dict[str, int] = {}
    with connect(db) as con:
        for code_id in code_ids:
            row = next(r for r in BRAVYI if r["code_id"] == code_id)
            G = ZmZn(row["group"]["ell"], row["group"]["m"])
            A_poly = Poly.from_string(row["polynomials"]["A"], G)
            B_poly = Poly.from_string(row["polynomials"]["B"], G)
            A_str = A_poly.canonical_string()
            B_str = B_poly.canonical_string()
            iid = canonical_hash(G.label(), A_str, B_str)
            inst = StoredInstance(
                instance_id=iid,
                code_id=code_id,
                group_struct=G.label(),
                ell=row["group"]["ell"], m=row["group"]["m"],
                n=row["parameters"]["n"], k=row["parameters"]["k"],
                A_poly=A_str, B_poly=B_str,
                A_weight=A_poly.weight(), B_weight=B_poly.weight(),
                d_exact=None, d_method=None,
            )
            upsert_instance(con, inst)
            truth[iid] = row["parameters"]["d"]
    return truth


@pytest.fixture
def small_bravyi_db(tmp_path: Path) -> tuple[Path, dict[str, int]]:
    """A DB with the 3 small Bravyi rows pending."""
    db = tmp_path / "test.duckdb"
    truth = _seed_pending_bravyi(
        db, ["bb_72_12_6", "bb_90_8_10", "bb_108_8_10"],
    )
    return db, truth


def test_parallel_fill_distances_writes_correct_d(small_bravyi_db):
    db, truth = small_bravyi_db
    runner = CliRunner()
    res = runner.invoke(main, [
        "fill-distances",
        "--db", str(db),
        "--max-n", "200",
        "--min-k", "1",
        "--timeout-per-instance", "120",
        "--workers", "3",
    ])
    assert res.exit_code == 0, f"command failed:\n{res.output}"

    with connect(db) as con:
        actual = {
            r[0]: r[1] for r in
            con.execute(
                "SELECT instance_id, d_exact FROM bb_instances"
            ).fetchall()
        }
    for iid, expected_d in truth.items():
        assert actual[iid] == expected_d, (
            f"row {iid[:8]}: got d_exact={actual[iid]}, expected {expected_d}"
        )


def test_parallel_fill_distances_records_method(small_bravyi_db):
    """On success, `d_method` is the cadical signature (matches the
    serial path)."""
    db, _truth = small_bravyi_db
    runner = CliRunner()
    res = runner.invoke(main, [
        "fill-distances", "--db", str(db),
        "--max-n", "200", "--min-k", "1",
        "--workers", "3",
    ])
    assert res.exit_code == 0, res.output
    with connect(db) as con:
        methods = [
            r[0] for r in
            con.execute(
                "SELECT d_method FROM bb_instances WHERE d_exact IS NOT NULL"
            ).fetchall()
        ]
    assert methods
    assert all(m.startswith("sat-cadical") for m in methods)


def test_parallel_fill_distances_serial_path_still_works(small_bravyi_db):
    """`--workers 1` routes through the serial path; results identical."""
    db, truth = small_bravyi_db
    runner = CliRunner()
    res = runner.invoke(main, [
        "fill-distances", "--db", str(db),
        "--max-n", "200", "--min-k", "1",
        "--workers", "1",
    ])
    assert res.exit_code == 0, res.output
    with connect(db) as con:
        actual = {
            r[0]: r[1] for r in
            con.execute("SELECT instance_id, d_exact FROM bb_instances").fetchall()
        }
    for iid, expected_d in truth.items():
        assert actual[iid] == expected_d


@pytest.mark.slow
def test_parallel_fill_distances_timeout_path_kills_worker(tmp_path):
    """A timeout shorter than the SAT solve marks the row and force-
    kills the worker.

    The smallest Bravyi instance that takes a non-trivial SAT time is
    bb_90_8_10 (~9s). A 1-second timeout reliably triggers the kill
    path. Marked slow because we still pay the spawn cost (~1s) for
    the killed subprocess.
    """
    db = tmp_path / "test.duckdb"
    _seed_pending_bravyi(db, ["bb_90_8_10"])
    runner = CliRunner()
    res = runner.invoke(main, [
        "fill-distances", "--db", str(db),
        "--max-n", "200", "--min-k", "1",
        "--timeout-per-instance", "1",
        "--workers", "2",
    ])
    assert res.exit_code == 0, res.output
    with connect(db) as con:
        row = con.execute(
            "SELECT d_exact, d_method FROM bb_instances"
        ).fetchone()
    assert row[0] is None, "d_exact should not be set on timeout"
    assert row[1] is not None and "timeout" in row[1].lower()


def test_parallel_fill_distances_no_pending_is_noop(tmp_path):
    """If every row already has d_exact, fill-distances does nothing."""
    db = tmp_path / "test.duckdb"
    # Seed bb_72_12_6 with d_exact already set.
    row = next(r for r in BRAVYI if r["code_id"] == "bb_72_12_6")
    G = ZmZn(row["group"]["ell"], row["group"]["m"])
    A_str = Poly.from_string(row["polynomials"]["A"], G).canonical_string()
    B_str = Poly.from_string(row["polynomials"]["B"], G).canonical_string()
    iid = canonical_hash(G.label(), A_str, B_str)
    inst = StoredInstance(
        instance_id=iid, code_id="bb_72_12_6",
        group_struct=G.label(),
        ell=6, m=6, n=72, k=12,
        A_poly=A_str, B_poly=B_str,
        A_weight=3, B_weight=3,
        d_exact=6, d_method="seeded",
    )
    with connect(db) as con:
        upsert_instance(con, inst)
    runner = CliRunner()
    res = runner.invoke(main, [
        "fill-distances", "--db", str(db),
        "--max-n", "200", "--min-k", "1",
        "--workers", "2",
    ])
    assert res.exit_code == 0
    assert "pending: 0 instances" in res.output
    # Existing d_exact untouched.
    with connect(db) as con:
        d, method = con.execute(
            "SELECT d_exact, d_method FROM bb_instances WHERE instance_id = ?",
            [iid],
        ).fetchone()
    assert d == 6
    assert method == "seeded"
