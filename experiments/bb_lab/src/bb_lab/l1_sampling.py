"""Random-sampling upper bound on the X-distance of a BB code.

For an upper bound `d_X ≤ w`, it is enough to exhibit a single Hamming-
weight-`w` vector `v ∈ ker(H_Z) \\ rowspan(H_X)` — i.e. a vector in a
nontrivial logical-Z coset. The exact `d_X` is `min { wt(v) | v in
nontrivial logical-Z coset }`; SAT computes it precisely
(`sat_distance.x_distance`) at exponential-in-`d` cost. L1 sampling
trades that for a cheap upper bound: draw many random coset elements,
keep the lightest.

We parameterise the coset by

    v = c · L_X  +  s · H_X        (mod 2)

with

    c ∈ F₂^k  nonzero          (which logical coset)
    s ∈ F₂^m  arbitrary         (which representative of that coset)

`L_X` is a k-row basis of `ker(H_Z) \\ rowspan(H_X)` (computed by
`find_logical_x`). Since each `L_X[i]` is in `ker(H_Z)` and not in
`rowspan(H_X)`, any nonzero `c · L_X + s · H_X` lies in a nontrivial
logical coset by construction — no per-sample validity check needed.

A uniformly-random `s` yields typical-weight `v` (≈ n/2 for random
codes), so we anneal `s`'s sparsity from low to high across trials —
sparse `s` is much more likely to land on low-weight `v`.

Cheap by design (10⁵ trials on n=288 takes well under a second), but
*not* tight: for `[[72,12,6]]` the bound it returns is usually 6
within a few thousand trials. For the gross `[[144,12,12]]` it's
typically 12. For larger instances where no SAT is available it's the
only quick handle on `d_X` we have.
"""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np

from .checks import CheckMatrices
from .linalg import nullspace_f2, quotient_complement_basis
from .sat_distance import find_logical_z


def find_logical_x(checks: CheckMatrices) -> np.ndarray:
    """k linearly-independent logical-X representatives, each in
    `ker(H_Z)` and outside `rowspan(H_X)`.

    Mirror of `sat_distance.find_logical_z` with the X/Z roles
    swapped; useful for sampling X-distance upper bounds because each
    `L_X[i] + s · H_X` is, by construction, a nontrivial X-logical.
    """
    ker_Z = nullspace_f2(checks.H_Z)
    return quotient_complement_basis(checks.H_X, ker_Z)


@dataclass(frozen=True, slots=True)
class SamplingResult:
    distance_ub: int
    witness: np.ndarray  # the achieving vector v
    n_samples_used: int


def l1_distance_ub(
    checks: CheckMatrices,
    *,
    n_samples: int = 100_000,
    seed: int = 0,
    sparsity_anneal: tuple[float, float] = (0.02, 0.5),
) -> SamplingResult:
    """Sample-based upper bound on `d_X`.

    `sparsity_anneal` is the (low, high) range of the stabilizer-
    combination Bernoulli rate `p`. Trial `t/n_samples` uses rate
    `low + (high − low) · t/n_samples`. The default `(0.02, 0.5)` gives
    good coverage of both "no/few stabilizer flips" (cheap pure-logical
    weights) and "broad mixing" (typical-weight regime).

    Raises if the code has `k = 0` (no nontrivial logicals).
    """
    rng = np.random.default_rng(seed)
    L_X = find_logical_x(checks)
    k, n = L_X.shape
    if k == 0:
        raise ValueError("code has k=0; d_X undefined")
    H_X = checks.H_X
    m = H_X.shape[0]

    low, high = sparsity_anneal
    best_w = n  # any weight ≤ n is trivially valid
    best_v: np.ndarray | None = None

    # Vectorize in batches of `B` trials at a time to keep numpy fast.
    B = max(1, min(4096, n_samples))
    trials_remaining = n_samples
    trial_idx = 0

    while trials_remaining > 0:
        batch = min(B, trials_remaining)
        # Random nonzero c ∈ F₂^k. With k ≥ 1, P(all-zero) = 1/2^k, so
        # almost always nonzero on the first try; resample the bad rows.
        c = rng.integers(0, 2, size=(batch, k), dtype=np.uint8)
        bad = (c.sum(axis=1) == 0)
        while bad.any():
            c[bad] = rng.integers(0, 2, size=(int(bad.sum()), k), dtype=np.uint8)
            bad = (c.sum(axis=1) == 0)
        # Annealing schedule: per-row sparsity p_t.
        ts = np.arange(trial_idx, trial_idx + batch, dtype=np.float64) / max(n_samples - 1, 1)
        ps = low + (high - low) * ts  # (batch,)
        # Random s with row-specific Bernoulli rate.
        u = rng.random(size=(batch, m))
        s = (u < ps[:, None]).astype(np.uint8)
        # v = c @ L_X + s @ H_X (mod 2). Both gemm-like ops over uint8.
        v = ((c @ L_X) + (s @ H_X)) & 1  # (batch, n)
        weights = v.sum(axis=1)
        # Strictly positive — should always hold since c != 0 means
        # v is in a nontrivial logical coset, but stabilizers can still
        # cancel within a coset. The minimum-weight representative of a
        # nontrivial coset has weight ≥ 1, so weight 0 would indicate
        # an internal error (or float artifact). Guard with > 0:
        valid = weights > 0
        if valid.any():
            idx = int(np.argmin(np.where(valid, weights, n + 1)))
            w = int(weights[idx])
            if w < best_w:
                best_w = w
                best_v = v[idx].copy()
        trials_remaining -= batch
        trial_idx += batch

    if best_v is None:
        # Pathological: all samples produced zero (would require s ·
        # H_X = c · L_X mod 2, which is exactly the trivial case ruled
        # out by c ≠ 0 — defensively, fall back to a raw L_X row).
        weights = L_X.sum(axis=1)
        idx = int(weights.argmin())
        best_v = L_X[idx]
        best_w = int(weights[idx])

    return SamplingResult(distance_ub=best_w, witness=best_v, n_samples_used=n_samples)


def verify_witness_in_nontrivial_coset(
    checks: CheckMatrices, v: np.ndarray
) -> bool:
    """Hard check: `v ∈ ker(H_Z)` and `v ∉ rowspan(H_X)`.

    For test use; verifies that a sampled witness is actually a
    nontrivial logical.
    """
    syndrome = (checks.H_Z @ v) % 2
    if syndrome.any():
        return False
    # v ∈ rowspan(H_X) iff there exists s with v = s @ H_X. Check by
    # extended row-reduction: solve s @ H_X = v over F_2 by augmenting.
    L_Z = find_logical_z(checks)
    # v ∉ rowspan(H_X) iff some L_Z[i] · v ≡ 1 (mod 2).
    return bool(((L_Z @ v) % 2).any())
