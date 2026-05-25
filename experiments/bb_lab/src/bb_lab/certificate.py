"""SAT distance certificates.

For v0 a "certificate" is a JSON file recording the minimum-weight
nontrivial-logical witness produced by the SAT search:

    {
      "schema_version": "bb-cert/v1",
      "code_id": "...",
      "n": ...,
      "distance": ...,
      "direction": "X",
      "witness_support": [i_1, i_2, ...],   # qubit indices set to 1
      "h_check_sha256": "...",              # over H_Z (the syndrome op)
      "l_logical_sha256": "...",            # over the logical-Z basis
      "solver": "cadical@1.9.5",
      "wall_seconds": ...,
    }

Anyone who has the (G, A, B) descriptor can rebuild `H_Z` and the
logical-Z basis, then independently verify

    H_Z · w  ≡  0   (mod 2)
    ∃ j     :  <L_Z[j], w>  ≡  1   (mod 2)
    |w|     =  distance

— a complete certificate of the SAT direction of the distance bound.
The UNSAT direction (proving no smaller logical exists) is currently
trusted to CaDiCaL; piping its LRAT output through `drat-trim` is a v1
follow-up that will populate a sibling `.drat` file alongside this JSON.
"""

from __future__ import annotations

import datetime as _dt
import hashlib
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Sequence

import numpy as np


SCHEMA_VERSION = "bb-cert/v1"


@dataclass(frozen=True, slots=True)
class UnsatProofRef:
    """A reference to a DRAT proof refuting a weight-bound CNF.

    Together with the corresponding CNF (same basename, `.cnf` suffix)
    this is a checkable certificate that no nontrivial logical of weight
    `weight_bound` or less exists. The whole chain
    `weight_bound = 1, 2, …, distance-1` certifies the lower bound
    `d ≥ distance`.
    """
    weight_bound: int
    drat_path: str           # relative to the certificate file's dir
    cnf_path: str            # relative to the certificate file's dir
    drat_sha256: str
    cnf_sha256: str


@dataclass(frozen=True, slots=True)
class WitnessCertificate:
    schema_version: str
    code_id: str
    n: int
    distance: int
    direction: str  # 'X' or 'Z'
    witness_support: tuple[int, ...]
    h_check_sha256: str
    l_logical_sha256: str
    solver: str
    wall_seconds: float
    emitted_at: str
    unsat_proofs: tuple[UnsatProofRef, ...] = ()

    def to_json(self) -> str:
        d = asdict(self)
        d["witness_support"] = list(self.witness_support)
        d["unsat_proofs"] = [asdict(p) for p in self.unsat_proofs]
        return json.dumps(d, indent=2, sort_keys=True)

    @classmethod
    def from_json(cls, text: str) -> "WitnessCertificate":
        d = json.loads(text)
        return cls(
            schema_version=d["schema_version"],
            code_id=d["code_id"],
            n=int(d["n"]),
            distance=int(d["distance"]),
            direction=d["direction"],
            witness_support=tuple(int(i) for i in d["witness_support"]),
            h_check_sha256=d["h_check_sha256"],
            l_logical_sha256=d["l_logical_sha256"],
            solver=d["solver"],
            wall_seconds=float(d["wall_seconds"]),
            emitted_at=d["emitted_at"],
            unsat_proofs=tuple(
                UnsatProofRef(**p) for p in d.get("unsat_proofs", [])
            ),
        )


def _matrix_hash(M: np.ndarray) -> str:
    return hashlib.sha256(np.ascontiguousarray(M & 1).tobytes()).hexdigest()


def make_certificate(
    *,
    code_id: str,
    H_check: np.ndarray,
    L_logical: np.ndarray,
    witness: np.ndarray,
    distance: int,
    direction: str,
    solver: str,
    wall_seconds: float,
    unsat_drat_paths: tuple[Path, ...] = (),
    cert_dir: Path | None = None,
) -> WitnessCertificate:
    """Build a `WitnessCertificate`.

    If `unsat_drat_paths` is supplied, each path must point at a `.drat`
    file with a sibling `.cnf`; both get hashed and referenced relative
    to `cert_dir` (so the cert can move with its proof bundle).
    """
    refs: list[UnsatProofRef] = []
    for p in unsat_drat_paths:
        p = Path(p)
        cnf = p.with_suffix(".cnf")
        if not cnf.exists():
            raise FileNotFoundError(f"DRAT {p} has no sibling CNF at {cnf}")
        # Extract weight bound from filename suffix `_w<N>.drat`
        stem = p.stem  # e.g. "bb_72_12_6_w5"
        try:
            wstr = stem.rsplit("_w", 1)[-1]
            w = int(wstr)
        except (IndexError, ValueError) as e:
            raise ValueError(f"cannot parse weight bound from {p.name}") from e
        if cert_dir is not None:
            drat_rel = str(p.relative_to(cert_dir))
            cnf_rel = str(cnf.relative_to(cert_dir))
        else:
            drat_rel = str(p)
            cnf_rel = str(cnf)
        refs.append(UnsatProofRef(
            weight_bound=w,
            drat_path=drat_rel,
            cnf_path=cnf_rel,
            drat_sha256=_file_hash(p),
            cnf_sha256=_file_hash(cnf),
        ))

    return WitnessCertificate(
        schema_version=SCHEMA_VERSION,
        code_id=code_id,
        n=int(witness.size),
        distance=distance,
        direction=direction,
        witness_support=tuple(int(i) for i in np.flatnonzero(witness)),
        h_check_sha256=_matrix_hash(H_check),
        l_logical_sha256=_matrix_hash(L_logical),
        solver=solver,
        wall_seconds=wall_seconds,
        emitted_at=_dt.datetime.now(_dt.UTC).isoformat(),
        unsat_proofs=tuple(refs),
    )


def _file_hash(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 16), b""):
            h.update(chunk)
    return h.hexdigest()


def verify_certificate(
    cert: WitnessCertificate,
    H_check: np.ndarray,
    L_logical: np.ndarray,
) -> None:
    """Independently check a certificate. Raises if the witness fails any
    of the three required properties (syndrome zero, anticommutes with
    some logical, weight equals claimed distance) or if the matrix
    hashes don't match what's recorded."""
    if cert.schema_version != SCHEMA_VERSION:
        raise ValueError(f"unknown cert schema {cert.schema_version!r}")
    if _matrix_hash(H_check) != cert.h_check_sha256:
        raise ValueError("H_check hash mismatch — certificate was built against a different check matrix")
    if _matrix_hash(L_logical) != cert.l_logical_sha256:
        raise ValueError("L_logical hash mismatch — certificate was built against a different logical basis")
    n = H_check.shape[1]
    if cert.n != n:
        raise ValueError(f"cert n={cert.n} ≠ H_check cols n={n}")
    w = np.zeros(n, dtype=np.uint8)
    for i in cert.witness_support:
        if not 0 <= i < n:
            raise ValueError(f"witness index {i} out of range")
        w[i] = 1
    if int(w.sum()) != cert.distance:
        raise ValueError(f"witness weight {int(w.sum())} ≠ claimed distance {cert.distance}")
    syndrome = (H_check @ w) % 2
    if syndrome.any():
        raise ValueError("witness has nonzero syndrome (not in ker(H_check))")
    anticomm = (L_logical @ w) % 2
    if not anticomm.any():
        raise ValueError("witness commutes with every logical (is a stabilizer, not a logical)")


def write_certificate(cert: WitnessCertificate, path: str | Path) -> Path:
    p = Path(path)
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(cert.to_json() + "\n")
    return p


def read_certificate(path: str | Path) -> WitnessCertificate:
    return WitnessCertificate.from_json(Path(path).read_text())
