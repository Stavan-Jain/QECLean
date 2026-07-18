"""Run the cover-side UNSAT@14 leg for f2a6f17e1c41ff96:y ONLY.

This is the certificate that subsumes the (M)-half for the Lean instance:
UNSAT at 14 on the [[300,8,16]] cover means NO nontrivial logical of
weight <= 14 exists at all — in particular none in the dangerous sector —
pinning d_X(cover) = 16 exactly (with the ladder witness) and upgrading
`DangerousFloorNZ 16` from assumption to certificate-checked.

Reuses the validated a15_cover_ladder machinery (CMS XOR-native backend,
parity makes w = 15 vacuous); appends to data/a15/cover_unsat14.jsonl.

Usage: uv run python scripts/a15_f2a6_cover_unsat_only.py
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import a15_cover_ladder as ladder

cells = [r for r in ladder.certified_cells()
         if r["instance_id"] == "f2a6f17e1c41ff96" and r["axis"] == "y"]
assert len(cells) == 1, cells
ladder.run_unsat(cells, backend="cms", timeout=6 * 3600.0, shard=None)
