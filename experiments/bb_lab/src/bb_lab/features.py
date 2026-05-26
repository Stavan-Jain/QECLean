"""Combinatorial features of BB-code Tanner graphs.

A BB code's Tanner graph is bipartite: `|G|` check nodes on one side
(rows of `H_X`), `2|G|` qubit nodes on the other (columns), with an
edge for each non-zero matrix entry.

Features computed:
- `tanner_girth(H)`: length of the shortest cycle in the Tanner graph,
  via BFS from each node. Cycles must have even length (bipartite).
  Returns `inf` for tree-like Tanner graphs (no cycles).
- `support_diameter(supp, G)`: max pairwise Cayley distance in the
  group between monomials in a polynomial's support. Cheap signal
  for "how spread out" a polynomial is.

Girth bounds the minimum-weight stopping-set / pseudo-codeword length;
LDPC theory says higher girth → better distance threshold and lower
error floor (under iterative decoding). Whether it predicts the
exact distance is open — that's what the Tier-2 mill should figure
out from the corpus.
"""

from __future__ import annotations

import math
from collections import deque

import numpy as np

from .group import AbelianGroup


def tanner_girth(H: np.ndarray) -> int | float:
    """Girth of the bipartite Tanner graph of check matrix `H` (rows =
    checks, cols = qubits). Returns `math.inf` if the graph has no
    cycles (a tree)."""
    n_checks, n_qubits = H.shape
    # Adjacency lists. Nodes are 0..n_checks-1 for checks,
    # n_checks..n_checks+n_qubits-1 for qubits.
    n_total = n_checks + n_qubits
    adj: list[list[int]] = [[] for _ in range(n_total)]
    for r in range(n_checks):
        for c in np.flatnonzero(H[r]):
            adj[r].append(n_checks + int(c))
            adj[n_checks + int(c)].append(r)

    best = math.inf
    for start in range(n_total):
        # BFS until we detect a cycle through `start`
        # Track parents to avoid trivial back-edges
        dist = [-1] * n_total
        parent = [-1] * n_total
        dist[start] = 0
        q = deque([start])
        while q:
            u = q.popleft()
            if dist[u] >= best // 2:
                break
            for v in adj[u]:
                if v == parent[u]:
                    continue
                if dist[v] == -1:
                    dist[v] = dist[u] + 1
                    parent[v] = u
                    q.append(v)
                else:
                    # Cycle: length = dist[u] + dist[v] + 1
                    cycle_len = dist[u] + dist[v] + 1
                    if cycle_len < best:
                        best = cycle_len
    return best


def min_weight_in_kernel(M: np.ndarray) -> int:
    """Minimum non-zero Hamming weight of a vector in `ker(M)` over F₂.

    `ker(M)` is treated as a linear code in F₂^n; this returns its
    minimum distance (≥ 1 for nontrivial kernels).

    The kernel is built once via `nullspace_f2`; we then walk all
    2^dim_ker − 1 non-empty subsets of basis vectors, XOR them, and
    track the minimum weight. For dim_ker ≤ ~22 this is fast; for
    larger kernels we'd want a Brouwer–Zimmermann-style algorithm but
    that's a v1.5 concern.

    Returns `n + 1` (a sentinel "no nonzero element found") if the
    kernel is trivial.
    """
    from .linalg import nullspace_f2
    basis = nullspace_f2(M)
    dim, n = basis.shape
    if dim == 0:
        return n + 1
    if dim > 22:
        raise ValueError(
            f"kernel dim {dim} > 22; brute-force enumeration is "
            "infeasible. Use a min-distance algorithm instead."
        )
    best = n + 1
    # Iterate Gray-code style: each step toggles one basis vector
    acc = np.zeros(n, dtype=np.uint8)
    for mask in range(1, 1 << dim):
        # Bit that toggled between mask-1 and mask
        toggled = (mask ^ (mask - 1)).bit_length() - 1
        acc ^= basis[toggled]
        w = int(acc.sum())
        if w < best:
            best = w
    return best


def support_diameter(
    support: frozenset[tuple[int, ...]] | tuple[tuple[int, ...], ...],
    G: AbelianGroup,
) -> int:
    """Max pairwise Cayley-metric distance in `G` over the polynomial's
    support, where Cayley distance is L1 on the cyclic factors (each
    coordinate taken mod the corresponding order)."""
    support = tuple(support)
    if len(support) < 2:
        return 0
    best = 0
    for i, g in enumerate(support):
        for h in support[i + 1:]:
            d = sum(
                min(abs(gi - hi), order - abs(gi - hi))
                for gi, hi, order in zip(g, h, G.orders)
            )
            if d > best:
                best = d
    return best
