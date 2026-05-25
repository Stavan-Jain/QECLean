"""End-to-end round-trip through the Lean handshake for the gross code.

  state.yaml  →  descriptor  →  JSON  →  descriptor  →  emitted .lean  →  `lake env lean`

The shell-out step requires that `QEC.Stabilizer.Framework.Homological`
has been built in this worktree (`lake build QEC.Stabilizer.Framework.Homological`).
The test is skipped if that build artifact is missing rather than
failing — CI environments without Lake should still pass the rest of
the suite.
"""

from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest

from bb_lab.lean_bridge import (
    BBDescriptor,
    SCHEMA_VERSION,
    descriptor_from_lean_defs,
    descriptor_from_state_yaml,
    emit_skeleton,
)


LAB_ROOT = Path(__file__).resolve().parent.parent
REPO_ROOT = LAB_ROOT.parent.parent


def _has_lake() -> bool:
    if shutil.which("lake") is None:
        return False
    # Has the dependency module been built?
    olean_glob = list(
        REPO_ROOT.glob(".lake/build/lib/lean/QEC/Stabilizer/Framework/Homological.olean")
    )
    return bool(olean_glob)


def test_descriptor_from_state_yaml():
    desc = descriptor_from_state_yaml(REPO_ROOT / "pipeline/attempts/gross/state.yaml")
    assert desc.code_id == "gross"
    assert desc.schema_version == SCHEMA_VERSION
    assert desc.group_orders == (12, 6)
    assert desc.n == 144
    assert set(desc.A_support) == {(3, 0), (0, 1), (0, 2)}
    assert set(desc.B_support) == {(0, 3), (1, 0), (2, 0)}


def test_descriptor_json_roundtrip():
    desc = descriptor_from_state_yaml(REPO_ROOT / "pipeline/attempts/gross/state.yaml")
    again = BBDescriptor.from_json(desc.to_json())
    # Polynomial supports + group + n + code_id + schema must round-trip.
    # The metadata is allowed to differ (transient stuff like timestamps).
    assert again.code_id == desc.code_id
    assert again.group_orders == desc.group_orders
    assert again.n == desc.n
    assert set(again.A_support) == set(desc.A_support)
    assert set(again.B_support) == set(desc.B_support)


def test_descriptor_from_lean_defs_matches():
    """Reverse-direction: parse the emitted Lean back to a descriptor and
    confirm the polynomial supports survive the trip."""
    desc = descriptor_from_state_yaml(REPO_ROOT / "pipeline/attempts/gross/state.yaml")
    emitted = emit_skeleton(desc, LAB_ROOT / "scratch" / "gross_for_parse.lean")
    parsed = descriptor_from_lean_defs(emitted.read_text(), code_id="gross")
    assert parsed.group_orders == desc.group_orders
    assert set(parsed.A_support) == set(desc.A_support)
    assert set(parsed.B_support) == set(desc.B_support)


def test_existing_lean_attempt_parses():
    """Sanity: parse the hand-written `attempt.lean` and recover the
    same supports as `state.yaml`. This is what guarantees the de-facto
    Lean convention agrees with our regex parser."""
    existing = REPO_ROOT / "pipeline/attempts/gross/approaches/A_camion_bch/attempt.lean"
    if not existing.exists():
        pytest.skip("hand-written attempt.lean missing in this checkout")
    desc = descriptor_from_lean_defs(existing.read_text(), code_id="gross")
    assert desc.group_orders == (12, 6)
    assert set(desc.A_support) == {(3, 0), (0, 1), (0, 2)}
    assert set(desc.B_support) == {(0, 3), (1, 0), (2, 0)}


def test_emitted_skeleton_compiles_under_lake():
    """The full v0 bridge gate. Requires Lake + a built
    `QEC.Stabilizer.Framework.Homological` artifact in this worktree.

    The test is skipped (not failed) if Lake or the artifact is missing,
    because environments without Lake should still pass the CI suite.
    Running this *should* be part of the v0 sign-off but is not blocking
    in pure-Python CI.
    """
    if not _has_lake():
        pytest.skip(
            "lake / QEC.Stabilizer.Framework.Homological.olean unavailable; "
            "run `lake build QEC.Stabilizer.Framework.Homological` in this worktree"
        )

    desc = descriptor_from_state_yaml(REPO_ROOT / "pipeline/attempts/gross/state.yaml")
    skeleton = emit_skeleton(desc, LAB_ROOT / "scratch" / "gross_roundtrip.lean")
    # Path lake-env-lean wants is the file path; cwd should be the repo root
    # so the lakefile is found and the import path is set up correctly.
    proc = subprocess.run(
        ["lake", "env", "lean", str(skeleton.relative_to(REPO_ROOT))],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        timeout=300,
    )
    assert proc.returncode == 0, (
        f"emitted skeleton did not compile:\n"
        f"--- stdout ---\n{proc.stdout}\n--- stderr ---\n{proc.stderr}"
    )
    # Lean emits nothing on success; on warnings it goes to stderr but
    # the return code is still 0. We accept warnings, only fail on errors.
    assert "error:" not in proc.stderr, (
        f"emitted skeleton has Lean errors:\n{proc.stderr}"
    )
