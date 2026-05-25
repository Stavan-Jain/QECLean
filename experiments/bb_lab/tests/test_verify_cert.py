"""End-to-end verification of the committed bb_72_12_6 DRAT certificate.

Mirrors what the eventual Lean LRAT consumer will do, but using
drat-trim externally instead of an in-kernel checker:

  1. Read the committed certificate JSON
  2. Re-derive H_check + L_logical from the same (G, A, B)
  3. Confirm the certificate's stored SHA256 hashes match
  4. Validate the SAT witness against the recomputed matrices
  5. Re-run drat-trim on every UNSAT DRAT proof
  6. Conclude `d_X(bb_72_12_6) = 6` from the combined evidence

If this test passes, the v1-track (b) soundness gate is closed end-to-end:
anyone with `cadical`, `drat-trim`, and our `(G, A, B)` can mechanically
reproduce the distance claim.
"""

from __future__ import annotations

import hashlib
import shutil
import subprocess
from pathlib import Path

import pytest

from bb_lab.certificate import read_certificate, verify_certificate
from bb_lab.checks import bb_check_matrices
from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.sat_distance import find_logical_z


LAB_ROOT = Path(__file__).resolve().parent.parent
DRAT_TRIM = shutil.which("drat-trim") or "/tmp/drat-trim/drat-trim"
HAS_DRAT_TRIM = Path(DRAT_TRIM).exists()


def _sha256_file(p: Path) -> str:
    h = hashlib.sha256()
    with p.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 16), b""):
            h.update(chunk)
    return h.hexdigest()


def _sha256_matrix(M) -> str:
    import numpy as np
    return hashlib.sha256(np.ascontiguousarray(M & 1).tobytes()).hexdigest()


def test_bb_72_committed_cert_witness_layer():
    """Step 1-4: witness + matrix-hash validation. Pure Python, fast."""
    cert_path = LAB_ROOT / "certificates" / "bb_72_12_6.cert.json"
    if not cert_path.exists():
        pytest.skip(
            "committed cert missing; run `bb-lab bravyi-check --quick --emit-proofs`"
        )
    cert = read_certificate(cert_path)
    assert cert.code_id == "bb_72_12_6"
    assert cert.distance == 6

    G = ZmZn(6, 6)
    A = Poly.from_string("x^3 + y + y^2", G)
    B = Poly.from_string("y^3 + x + x^2", G)
    checks = bb_check_matrices(A, B)
    L_Z = find_logical_z(checks)

    # Hash agreement = "this certificate is about this code"
    assert _sha256_matrix(checks.H_Z) == cert.h_check_sha256
    assert _sha256_matrix(L_Z) == cert.l_logical_sha256

    # Witness is a legitimate weight-6 nontrivial logical
    verify_certificate(cert, checks.H_Z, L_Z)


@pytest.mark.skipif(
    not HAS_DRAT_TRIM,
    reason="drat-trim not available — build via `cd /tmp && "
           "git clone https://github.com/marijnheule/drat-trim && "
           "cd drat-trim && cc -O2 -o drat-trim drat-trim.c`",
)
def test_bb_72_committed_cert_drat_layer():
    """Step 5-6: every committed DRAT proof passes drat-trim, and the
    weight bounds chain together into the final distance claim."""
    cert_path = LAB_ROOT / "certificates" / "bb_72_12_6.cert.json"
    if not cert_path.exists():
        pytest.skip("committed cert missing")
    cert = read_certificate(cert_path)
    cert_dir = cert_path.parent

    seen_bounds = set()
    for ref in cert.unsat_proofs:
        drat = cert_dir / ref.drat_path
        cnf = cert_dir / ref.cnf_path
        assert drat.exists(), f"missing committed DRAT {drat}"
        assert cnf.exists(), f"missing committed CNF {cnf}"
        # Files haven't been tampered with
        assert _sha256_file(drat) == ref.drat_sha256, (
            f"DRAT file content changed since cert was written: {drat}"
        )
        assert _sha256_file(cnf) == ref.cnf_sha256
        # drat-trim accepts the proof
        proc = subprocess.run(
            [DRAT_TRIM, str(cnf), str(drat)],
            capture_output=True, text=True, timeout=120,
        )
        assert "s VERIFIED" in proc.stdout, (
            f"drat-trim rejected w={ref.weight_bound}:\n{proc.stdout[-500:]}"
        )
        assert "s NOT VERIFIED" not in proc.stdout
        seen_bounds.add(ref.weight_bound)

    # The chain {w=1, 2, ..., d-1} = {1, ..., 5} must all be present
    assert seen_bounds == {1, 2, 3, 4, 5}, (
        f"the chain of UNSAT bounds w=1..d-1=5 is incomplete; "
        f"have {sorted(seen_bounds)}"
    )
