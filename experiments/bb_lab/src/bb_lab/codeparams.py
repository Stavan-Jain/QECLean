"""Compute (n, k) for a BB code from its check matrices.

For a CSS code, `k = n − rank₂(H_X) − rank₂(H_Z)`. BB codes have
`rank(H_X) = rank(H_Z)` by symmetry, so equivalently `k = n − 2·rank(H_X)`,
but the formula below works without that assumption.
"""

from __future__ import annotations

from dataclasses import dataclass

from .checks import CheckMatrices
from .linalg import rank_f2


@dataclass(frozen=True, slots=True)
class CodeParams:
    n: int
    k: int
    rank_HX: int
    rank_HZ: int


def code_params(checks: CheckMatrices) -> CodeParams:
    n = checks.num_qubits
    rX = rank_f2(checks.H_X)
    rZ = rank_f2(checks.H_Z)
    k = n - rX - rZ
    if k < 0:
        raise AssertionError(
            f"computed k = {k} < 0; "
            f"n={n}, rank(H_X)={rX}, rank(H_Z)={rZ}. "
            "Either H_X·H_Zᵀ ≠ 0 (CSS commutation broken) or rank computation is wrong."
        )
    return CodeParams(n=n, k=k, rank_HX=rX, rank_HZ=rZ)
