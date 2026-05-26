"""SAT-compute distance for the 3 small Bravyi instances; gate the v0 substrate.

Expected wall times (CaDiCaL 1.9.5 on Apple Silicon, single-thread):
  [[72,12,6]]    ~0.1 s
  [[90,8,10]]    ~10 s
  [[108,8,10]]   ~6 s

Larger Bravyi instances are marked `slow` and excluded from default CI;
run them via `pytest -m slow` or `bb-lab bravyi-check --full`.
"""

from __future__ import annotations

import numpy as np
import pytest

from bb_lab.checks import bb_check_matrices
from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.sat_distance import find_logical_z, x_distance


def _build_checks(row):
    G = ZmZn(row["group"]["ell"], row["group"]["m"])
    A = Poly.from_string(row["polynomials"]["A"], G)
    B = Poly.from_string(row["polynomials"]["B"], G)
    return bb_check_matrices(A, B)


def _verify_witness(checks, v: np.ndarray) -> None:
    """Independent check that the SAT witness really is a nontrivial X-logical."""
    syndrome = (checks.H_Z @ v) % 2
    assert not syndrome.any(), "witness has nonzero H_Z syndrome (is not in ker(H_Z))"
    L_Z = find_logical_z(checks)
    anticomm = (L_Z @ v) % 2
    assert anticomm.any(), (
        "witness commutes with every logical-Z (so it IS in rowspan(H_X), "
        "i.e. a stabilizer — not a true logical)"
    )


@pytest.mark.parametrize("idx,name", [
    (0, "bb_72_12_6"),
    (1, "bb_90_8_10"),
    (2, "bb_108_8_10"),
])
def test_distance_matches_published(bravyi_table, idx, name):
    row = bravyi_table[idx]
    assert row["code_id"] == name, "fixture ordering changed"
    checks = _build_checks(row)
    result = x_distance(checks)
    assert result.distance == row["parameters"]["d"], (
        f"{name}: SAT distance {result.distance}, "
        f"published {row['parameters']['d']}"
    )
    _verify_witness(checks, result.witness)


@pytest.mark.slow
def test_distance_gross_144():
    """[[144,12,12]] — the IBM gross code. Heroic; minutes-to-hours."""
    import yaml
    from pathlib import Path
    LAB = Path(__file__).resolve().parent.parent
    rows = yaml.safe_load((LAB / "instances" / "bravyi_table.yaml").read_text())["instances"]
    row = next(r for r in rows if r["code_id"] == "gross")
    checks = _build_checks(row)
    result = x_distance(checks)
    assert result.distance == 12
    _verify_witness(checks, result.witness)


@pytest.mark.slow
def test_distance_bb_288():
    """[[288,12,18]]. Heroic; multi-hour."""
    import yaml
    from pathlib import Path
    LAB = Path(__file__).resolve().parent.parent
    rows = yaml.safe_load((LAB / "instances" / "bravyi_table.yaml").read_text())["instances"]
    row = next(r for r in rows if r["code_id"] == "bb_288_12_18")
    checks = _build_checks(row)
    result = x_distance(checks)
    assert result.distance == 18
    _verify_witness(checks, result.witness)
