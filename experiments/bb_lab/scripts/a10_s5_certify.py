"""A10 S5 — archival certification of selected rescues.

For chosen (base, class, twist) rescues from the S4 screens, re-run the
full distance ladder with LRAT proof emission (cadical CLI): UNSAT
proofs for every weight 1..2d-1 plus the weight-2d SAT witness give a
complete distance certificate, independently re-checkable.  Also
re-verifies the witness in numpy (kernel membership, logical pairing,
weight) — the same checks a Lean `decide` would perform.

    uv run python scripts/a10_s5_certify.py \
        --ell 6 --m 6 --A "y^3 + x + x^2" --B "1 + x*y^5 + x^2*y" \
        --base-id hit2 --d-base 6 --cls 1 0 --epsA 0 0 0 --epsB 0 0 1
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

import numpy as np

LAB_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LAB_ROOT / "src"))
sys.path.insert(0, str(LAB_ROOT / "scripts"))

from bb_lab.group import AbelianGroup
from bb_lab.linalg import rank_f2
from bb_lab.poly import Poly
from bb_lab.sat_distance import x_distance, find_logical_z

from a10_descent_covers import descent_checks, code_k, twisted_lift

PROOF_DIR = LAB_ROOT / "data" / "a10" / "certs"


def verify_witness(checks, v: np.ndarray) -> dict:
    """Numpy re-verification of a claimed nontrivial X-logical."""
    L_Z = find_logical_z(checks)
    syndrome = (checks.H_Z @ v) % 2
    pairings = (L_Z @ v) % 2
    in_rowspan = (
        rank_f2(np.vstack([checks.H_X, v])) == rank_f2(checks.H_X)
    )
    return {
        "weight": int(v.sum()),
        "in_ker_HZ": not syndrome.any(),
        "anticommutes_with_a_logical": bool(pairings.any()),
        "in_rowspan_HX": bool(in_rowspan),
        "is_nontrivial_logical": (not syndrome.any())
        and bool(pairings.any())
        and not in_rowspan,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--ell", type=int, required=True)
    ap.add_argument("--m", type=int, required=True)
    ap.add_argument("--A", required=True)
    ap.add_argument("--B", required=True)
    ap.add_argument("--base-id", required=True)
    ap.add_argument("--d-base", type=int, required=True)
    ap.add_argument("--cls", type=int, nargs=2, required=True)
    ap.add_argument("--epsA", type=int, nargs="+", required=True)
    ap.add_argument("--epsB", type=int, nargs="+", required=True)
    args = ap.parse_args()

    H = AbelianGroup((args.ell, args.m))
    A = Poly.from_string(args.A, H)
    B = Poly.from_string(args.B, H)
    cls = tuple(args.cls)
    epsA, epsB = tuple(args.epsA), tuple(args.epsB)
    checks, Gc = descent_checks(A, B, cls, epsA, epsB)
    k = code_k(checks)
    target = 2 * args.d_base
    cert_id = (
        f"{args.base_id}_c{cls[0]}{cls[1]}"
        f"_eA{''.join(map(str, epsA))}_eB{''.join(map(str, epsB))}"
    )
    proof_dir = PROOF_DIR / cert_id
    proof_dir.mkdir(parents=True, exist_ok=True)

    print(f"[{cert_id}] n={checks.num_qubits} k={k}; ladder to {target} with LRAT ...")
    t0 = time.time()
    res = x_distance(
        checks,
        weight_upper_bound=target,
        verbose=True,
        proof_dir=proof_dir,
        code_id=cert_id,
    )
    wv = verify_witness(checks, res.witness)
    out = {
        "cert_id": cert_id,
        "base_id": args.base_id,
        "group": [args.ell, args.m],
        "A": args.A,
        "B": args.B,
        "cls": list(cls),
        "epsA": list(epsA),
        "epsB": list(epsB),
        "cover_A_support": sorted(map(list, twisted_lift(A, Gc, epsA).support)),
        "cover_B_support": sorted(map(list, twisted_lift(B, Gc, epsB).support)),
        "n": checks.num_qubits,
        "k": k,
        "distance": res.distance,
        "witness_qubits": [int(i) for i in np.flatnonzero(res.witness)],
        "witness_verification": wv,
        "unsat_proofs": [str(p.relative_to(LAB_ROOT)) for p in res.unsat_proof_paths],
        "secs": round(time.time() - t0, 1),
    }
    out_path = proof_dir / "certificate.json"
    out_path.write_text(json.dumps(out, indent=2))
    print(json.dumps({k: v for k, v in out.items() if k != "witness_qubits"}, indent=2))
    print(f"wrote {out_path}")
    assert out["distance"] == target and wv["is_nontrivial_logical"]
    print("CERTIFIED: d(cover) = 2*d(base), witness verified.")


if __name__ == "__main__":
    main()
