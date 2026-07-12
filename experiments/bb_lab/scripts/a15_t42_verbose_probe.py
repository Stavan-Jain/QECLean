#!/usr/bin/env python3
"""One-member verbose distance probe: per-weight SAT timing (T4.2 tuning)."""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "src"))

from bb_lab.checks import bb_check_matrices
from bb_lab.codeparams import code_params
from bb_lab.group import AbelianGroup
from bb_lab.poly import Poly
from bb_lab.sat_distance import x_distance

row = json.loads(sys.argv[1])
ub = int(sys.argv[2]) if len(sys.argv) > 2 else 10
ell, m = row["frame"]
G = AbelianGroup((ell, m))
A = Poly.from_string(row["A"], G)
B = Poly.from_string(row["B"], G)
checks = bb_check_matrices(A, B)
print(f"frame Z{ell}xZ{m}, n={2*ell*m}, k={code_params(checks).k}", flush=True)
try:
    res = x_distance(checks, weight_lower_bound=2, weight_upper_bound=ub,
                     verbose=True)
    print(f"d = {res.distance}")
except RuntimeError:
    print(f"d > {ub}")
