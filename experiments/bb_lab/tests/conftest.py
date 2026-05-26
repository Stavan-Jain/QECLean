"""Test fixtures shared across v0 tests."""

from __future__ import annotations

from pathlib import Path

import pytest
import yaml


LAB_ROOT = Path(__file__).resolve().parent.parent
REPO_ROOT = LAB_ROOT.parent.parent  # experiments/bb_lab -> repo root


@pytest.fixture(scope="session")
def bravyi_table() -> list[dict]:
    """The five Bravyi BB instances from `instances/bravyi_table.yaml`."""
    path = LAB_ROOT / "instances" / "bravyi_table.yaml"
    data = yaml.safe_load(path.read_text())
    assert data["schema_version"].startswith("bb-instance/")
    return data["instances"]


@pytest.fixture(scope="session")
def gross_state_yaml() -> dict:
    """The actual `pipeline/attempts/gross/state.yaml` from the repo.

    This is the production polynomial-string source for the gross code;
    the round-trip test consumes it directly.
    """
    path = REPO_ROOT / "pipeline" / "attempts" / "gross" / "state.yaml"
    return yaml.safe_load(path.read_text())
