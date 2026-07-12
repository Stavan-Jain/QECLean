"""SAT-based exact distance for CSS codes.

A nontrivial X-logical is an `n`-bit vector `v` satisfying

  1.  `H_Z · v ≡ 0  (mod 2)`             (commutes with all Z-stabilizers)
  2.  `<L_Z[j], v> ≡ 1  (mod 2)` for at least one logical-Z basis
      vector `L_Z[j]`                    (not in `rowspan(H_X)`)

`d_X = min |v|` over such `v`. By BB symmetry `d_Z = d_X`, so the
distance of a BB CSS code is `d_X`.

Encoding:
- One Boolean variable `v_i ∈ {0,1}` per qubit.
- For each row `r` of `H_Z`: `⊕_i (H_Z[r,i] · v_i) = 0`, Tseitin-encoded
  via a chain of fresh XOR auxiliaries.
- For each logical row `L_Z[j]`: chain XOR → output literal `a_j`.
- Add clause `a_1 ∨ a_2 ∨ … ∨ a_k`  (anticommute with at least one).
- Cardinality constraint `∑ v_i ≤ w`  (`pysat.card.CardEnc`, sequential
  counter).
- Iterate `w = 1, 2, …` and return the first `w` that is SAT.

The witness model `v` from the SAT direction is itself a verifiable
certificate (an explicit nontrivial logical at the claimed weight).

For the UNSAT direction (lower-bounding the distance), pass
`proof_dir=<path>` to `x_distance` and LRAT proofs + DIMACS CNFs are
written to `<proof_dir>/<code_id>_w<weight>.{cnf,lrat}`. Those proofs
are the v1 hand-off to a future in-kernel Lean LRAT consumer.

**Backend split**: when proofs are requested the lab shells out to the
`cadical` binary (CaDiCaL 3.0 via Homebrew) — pysat's bundled CaDiCaL
has a stdio-buffering bug that truncates mid-sized DRAT proofs. When
no proof is requested the in-process pysat path is used (~3× faster on
small instances, no subprocess overhead).
"""

from __future__ import annotations

import shutil
import subprocess
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable

import numpy as np

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195

from .checks import CheckMatrices
from .linalg import nullspace_f2, quotient_complement_basis


CADICAL_BINARY = shutil.which("cadical")  # None if not installed

try:  # CryptoMiniSat with native XOR clauses — the A15 lesson: CaDiCaL
    # on Tseitin-encoded XOR chains is intractable on the UNSAT rounds
    # of BB distance instances; CMS handles the parity rows natively.
    import pycryptosat
    _HAVE_CMS = True
except ImportError:
    _HAVE_CMS = False


@dataclass(frozen=True, slots=True)
class DistanceResult:
    distance: int
    witness: np.ndarray         # shape (n,), uint8; weight == distance
    weight_threshold_tried: int
    direction: str              # 'X' or 'Z'
    unsat_proof_paths: tuple[Path, ...] = ()  # DRAT proofs, one per UNSAT weight


def _xor_chain(
    lits: Iterable[int], pool: IDPool, cnf: CNF
) -> int | None:
    """Tseitin-encode the XOR of `lits`. Return the output literal,
    or None if `lits` is empty (XOR of empty list = 0, i.e. False)."""
    seq = list(lits)
    if not seq:
        return None
    acc = seq[0]
    for x in seq[1:]:
        new = pool.id()
        # new ≡ acc ⊕ x
        cnf.append([-new, -acc, -x])
        cnf.append([-new,  acc,  x])
        cnf.append([ new, -acc,  x])
        cnf.append([ new,  acc, -x])
        acc = new
    return acc


def _build_cnf_at_weight(
    H_check: np.ndarray,
    L_logical: np.ndarray,
    weight: int,
) -> tuple[CNF, list[int]]:
    """Build the CNF asking for a nontrivial logical of weight ≤ `weight`.

    Returns (cnf, qubit_vars) so the caller can decode the model.
    """
    n = H_check.shape[1]
    pool = IDPool()
    qubit_vars = [pool.id() for _ in range(n)]

    cnf = CNF()

    # 1.  Syndrome constraint: each row of H_check XORs to 0.
    for row in H_check:
        idx = np.flatnonzero(row)
        if idx.size == 0:
            continue
        out = _xor_chain((qubit_vars[i] for i in idx), pool, cnf)
        if out is not None:
            cnf.append([-out])  # force XOR ≡ 0

    # 2.  At least one logical-Z anticommutes with v.
    a_outs: list[int] = []
    for L in L_logical:
        idx = np.flatnonzero(L)
        if idx.size == 0:
            continue
        out = _xor_chain((qubit_vars[i] for i in idx), pool, cnf)
        if out is not None:
            a_outs.append(out)
    if not a_outs:
        raise AssertionError("no non-trivial logicals to witness against")
    cnf.append(a_outs)

    # 3.  Cardinality: ∑ v ≤ weight (sequential counter, no auxiliaries
    #     leak out the qubit_vars vector we care about).
    if weight < n:
        card = CardEnc.atmost(
            lits=qubit_vars,
            bound=weight,
            vpool=pool,
            encoding=EncType.seqcounter,
        )
        cnf.extend(card.clauses)
    # If weight == n the constraint is vacuous; skip.

    return cnf, qubit_vars


def _write_dimacs(cnf: CNF, path: Path) -> None:
    """Emit a DIMACS-format CNF file (so the proof can be checked against
    the formula it refutes)."""
    nv = cnf.nv
    nc = len(cnf.clauses)
    with path.open("w") as f:
        f.write(f"p cnf {nv} {nc}\n")
        for clause in cnf.clauses:
            f.write(" ".join(str(int(lit)) for lit in clause) + " 0\n")


def _parse_cadical_witness(stdout: str, qubit_vars: list[int]) -> np.ndarray:
    """Parse CaDiCaL's DIMACS-competition-format witness lines (`v ...`)."""
    truth: dict[int, bool] = {}
    for line in stdout.splitlines():
        if not line.startswith("v "):
            continue
        for tok in line[2:].split():
            lit = int(tok)
            if lit == 0:
                continue
            truth[abs(lit)] = lit > 0
    return np.array(
        [1 if truth.get(qv, False) else 0 for qv in qubit_vars],
        dtype=np.uint8,
    )


def _solve_at_weight_cms(
    H_check: np.ndarray,
    L_logical: np.ndarray,
    weight: int,
) -> tuple[np.ndarray | None, None]:
    """CryptoMiniSat backend: same instance as `_build_cnf_at_weight`
    but with the parity constraints as native XOR clauses.

    Each check row becomes `add_xor_clause(row_vars, rhs=False)`; each
    logical rep gets an indicator `a` via `XOR(row_vars ∪ {a}) = 0`
    (i.e. a ≡ XOR(row_vars)), and one clause ⋁ a_i asks that some
    logical anticommutes. Cardinality stays a seqcounter CNF over the
    shared IDPool, so variable spaces cannot collide."""
    n = H_check.shape[1]
    pool = IDPool()
    qubit_vars = [pool.id() for _ in range(n)]
    solver = pycryptosat.Solver()

    for row in H_check:
        idx = np.flatnonzero(row)
        if idx.size:
            solver.add_xor_clause([qubit_vars[i] for i in idx], False)

    a_outs: list[int] = []
    for L in L_logical:
        idx = np.flatnonzero(L)
        if idx.size == 0:
            continue
        a = pool.id()
        solver.add_xor_clause([qubit_vars[i] for i in idx] + [a], False)
        a_outs.append(a)
    if not a_outs:
        raise AssertionError("no non-trivial logicals to witness against")
    solver.add_clause(a_outs)

    if weight < n:
        card = CardEnc.atmost(
            lits=qubit_vars,
            bound=weight,
            vpool=pool,
            encoding=EncType.seqcounter,
        )
        for cl in card.clauses:
            solver.add_clause(cl)

    sat, model = solver.solve()
    if not sat:
        return None, None
    v = np.array(
        [1 if model[qv] else 0 for qv in qubit_vars], dtype=np.uint8
    )
    return v, None


def _solve_via_cadical_cli(
    cnf: CNF,
    qubit_vars: list[int],
    *,
    code_id: str,
    weight: int,
    proof_dir: Path,
) -> tuple[np.ndarray | None, Path | None]:
    """Run the `cadical` CLI on `cnf`, capturing LRAT proof on UNSAT.

    Returns `(witness, proof_path)`:
      - `(np.ndarray, None)` on SAT (witness recovered from stdout)
      - `(None, Path)` on UNSAT (LRAT proof at `<proof_dir>/<code_id>_w<weight>.lrat`,
        with sibling `.cnf`)
    """
    if CADICAL_BINARY is None:
        raise RuntimeError(
            "cadical CLI not found on PATH. Install via `brew install cadical` "
            "(macOS) or build from source. The proof-emitting path requires it."
        )
    proof_dir = Path(proof_dir)
    proof_dir.mkdir(parents=True, exist_ok=True)
    base = proof_dir / f"{code_id}_w{weight}"
    cnf_path = base.with_suffix(".cnf")
    # CaDiCaL writes binary DRAT by default; `--no-binary` switches to text.
    # We use text DRAT because `drat-trim` accepts it directly for
    # verification, and we can convert text DRAT → LRAT downstream via
    # `drat-trim -L <out.lrat>` for the Lean consumer.
    drat_path = base.with_suffix(".drat")
    _write_dimacs(cnf, cnf_path)
    proc = subprocess.run(
        [CADICAL_BINARY, "--no-binary", str(cnf_path), str(drat_path)],
        capture_output=True,
        text=True,
    )
    # CaDiCaL exit codes: 10 = SAT, 20 = UNSAT, anything else is an error.
    if proc.returncode == 10:
        witness = _parse_cadical_witness(proc.stdout, qubit_vars)
        # On SAT we don't need either artifact — the witness is the
        # certificate; the CNF/DRAT pair only carries information for
        # UNSAT cases.
        for stale in (drat_path, cnf_path):
            if stale.exists():
                stale.unlink()
        return witness, None
    elif proc.returncode == 20:
        if not drat_path.exists() or drat_path.stat().st_size == 0:
            raise RuntimeError(
                f"cadical UNSAT but proof file {drat_path} missing or empty.\n"
                f"stdout:\n{proc.stdout[-2000:]}\n"
                f"stderr:\n{proc.stderr[-2000:]}"
            )
        return None, drat_path
    raise RuntimeError(
        f"cadical exited with code {proc.returncode} (not SAT=10 or UNSAT=20).\n"
        f"stdout:\n{proc.stdout[-2000:]}\n"
        f"stderr:\n{proc.stderr[-2000:]}"
    )


def _solve_at_weight(
    H_check: np.ndarray,
    L_logical: np.ndarray,
    weight: int,
    *,
    proof_dir: Path | None = None,
    code_id: str = "code",
) -> tuple[np.ndarray | None, Path | None]:
    """Return `(witness, proof_path)`.

    `witness` is a weight-≤`weight` vector on SAT, else `None`.
    `proof_path` is the path to an LRAT proof if `proof_dir` is set and
    the instance was UNSAT, else `None`.

    Backend choice:
      - `proof_dir is None`, pycryptosat importable: in-process
        CryptoMiniSat with native XOR rows (fastest, no proof).
      - `proof_dir is None`, no pycryptosat: pysat in-process CaDiCaL.
      - `proof_dir is not None`: `cadical` CLI subprocess (slower, reliable
        LRAT emission).
    """
    if proof_dir is None and _HAVE_CMS:
        return _solve_at_weight_cms(H_check, L_logical, weight)

    cnf, qubit_vars = _build_cnf_at_weight(H_check, L_logical, weight)

    if proof_dir is not None:
        return _solve_via_cadical_cli(
            cnf, qubit_vars,
            code_id=code_id, weight=weight, proof_dir=proof_dir,
        )

    # No proof requested → fast pysat in-process path.
    solver = Cadical195(bootstrap_with=cnf.clauses)
    try:
        if not solver.solve():
            return None, None
        model = solver.get_model()
        truth = {abs(lit): lit > 0 for lit in model}
        v = np.array(
            [1 if truth.get(qv, False) else 0 for qv in qubit_vars],
            dtype=np.uint8,
        )
        return v, None
    finally:
        solver.delete()


def find_logical_z(checks: CheckMatrices) -> np.ndarray:
    """k linearly-independent logical-Z representatives, each in
    `ker(H_X)` and outside `rowspan(H_Z)`."""
    ker_X = nullspace_f2(checks.H_X)
    return quotient_complement_basis(checks.H_Z, ker_X)


def x_distance(
    checks: CheckMatrices,
    *,
    weight_lower_bound: int = 1,
    weight_upper_bound: int | None = None,
    verbose: bool = False,
    proof_dir: Path | str | None = None,
    code_id: str = "code",
) -> DistanceResult:
    """Compute `d_X` exactly via iterated SAT calls.

    `weight_lower_bound` lets the caller skip cheap UNSAT calls when a
    lower bound is already known (e.g. from a BPT-style argument).
    `weight_upper_bound` (default `n`) caps the search.
    `verbose=True` prints one line per weight iteration with the elapsed
    wall time — useful for long-running heroic instances.
    `proof_dir=<path>` enables emission of LRAT proofs + DIMACS CNFs for
    every UNSAT call; combined with the SAT witness this gives a full
    distance certificate. Requires the `cadical` CLI.
    """
    import sys
    import time as _time
    n = checks.num_qubits
    if weight_upper_bound is None:
        weight_upper_bound = n
    L_Z = find_logical_z(checks)
    if L_Z.shape[0] == 0:
        raise ValueError("code has k = 0; distance is undefined")

    proof_paths: list[Path] = []
    proof_dir_path = Path(proof_dir) if proof_dir is not None else None

    for w in range(weight_lower_bound, weight_upper_bound + 1):
        if verbose:
            t0 = _time.time()
        witness, proof_path = _solve_at_weight(
            checks.H_Z, L_Z, w,
            proof_dir=proof_dir_path, code_id=code_id,
        )
        if proof_path is not None:
            proof_paths.append(proof_path)
        if verbose:
            dt = _time.time() - t0
            outcome = "SAT  ✓" if witness is not None else "UNSAT"
            extra = f"  lrat={proof_path.name}" if proof_path else ""
            print(f"  [w ≤ {w:3d}]  {outcome}  ({dt:7.2f}s){extra}", flush=True)
            sys.stdout.flush()
        if witness is not None:
            actual_w = int(witness.sum())
            if actual_w == 0:
                raise AssertionError(
                    "SAT returned all-zero witness; encoding is wrong"
                )
            assert actual_w <= w
            return DistanceResult(
                distance=actual_w,
                witness=witness,
                weight_threshold_tried=w,
                direction="X",
                unsat_proof_paths=tuple(proof_paths),
            )
    raise RuntimeError(
        f"no nontrivial logical found at weight ≤ {weight_upper_bound}; "
        "either weight_upper_bound is too low or the code has no logicals"
    )
