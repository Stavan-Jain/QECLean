"""Weight invariants for BB-code distance bound research.

A **weight invariant** is a quantity defined via the minimum non-zero
Hamming weight of some linear subspace (a kernel, a coset, a defined
subspace within an isotypical decomposition). Weight invariants can
appear on the right-hand side of a `d ≥ ...` bound — they bound
minimum distance.

Contrast with **dimension invariants** (rank, dim ker, orbit sizes,
multiplicities) which bound k-related quantities and cannot directly
bound d. The Jacobson-radical bound from Tier-2 Round 1 was a
dimension invariant put on the RHS of `d ≥ ...`, which is why it
failed (see `pipeline/attempts/bb_distance_conjecture/result.md` and
HANDOFF.md §6h).

This module provides:

- `per_orbit_dual_distance(A, G)`: for each Frobenius orbit O on G_odd
  where A vanishes, the minimum non-zero Hamming weight of any vector
  in the O-isotypic component of `ker(M_A)`. Returns a dict
  `{orbit_frozenset: distance}`, with non-vanishing orbits not in the
  output (i.e. their distance is `+∞`, no nonzero vector to take).

- `tz_lower_bound(A, B)`: Lin-Pryadko Statement 12,
  `⌈min(d_A^⊥, d_B^⊥) / c⌉` with `c = |G_a ∩ G_b|`. Standalone
  callable refactor of the lambda in `scripts/tier2_candidates_lit.py`.

- `bch_per_orbit_lower_bound(poly, G)`: BCH/Hartmann-Tzeng-style
  lower bound on `d_A^⊥`, derived from the cyclotomic-coset structure
  of the support of `poly` rather than from explicit kernel enumeration.
  For multiplicative-cyclic G this is a true classical-cyclic-code BCH
  bound; for multi-cyclic G the per-axis projection bound applies.

- `joint_kernel_min_weight(A, B, G)`: minimum non-zero Hamming weight
  of any element of `ker(M_A) ∩ ker(M_B)`. This is a *weight invariant
  of the joint kernel as a linear code*. (Note: this UPPER-bounds `d_X`
  because the joint kernel contains the logical-X coset reps. Useful
  diagnostically — not a lower-bound RHS candidate.)

All four functions are designed to be **callable on any BB instance
in the corpus** with reasonable runtime up to `|G| ≤ 72` (gross
parameters). For larger groups, per-orbit enumeration may be expensive;
callers should check `dim_ker_A` first.

The functions never modify the corpus DB; they compute on-the-fly.
"""

from __future__ import annotations

import math
from math import gcd
from typing import Sequence

import numpy as np

from .algebraic_features import (
    _PRIM_POLYS,
    _chi_order_in_g_odd,
    _fld_mul,
    _fld_pow,
    _g_odd_orders,
    _order_2_mod,
    _project_to_g_odd,
    g_odd_frobenius_orbits,
    jacobson_radical_depth,
)
from .checks import circulant
from .features import min_weight_in_kernel
from .group import AbelianGroup
from .linalg import nullspace_f2
from .poly import Poly


# ---------------------------------------------------------------------------
# Helpers: character constraint matrices
# ---------------------------------------------------------------------------


def _char_constraint_rows_g_odd(
    G: AbelianGroup, orbit_rep_g_odd: tuple[int, ...]
) -> np.ndarray:
    """Build the F_2-linear constraints "<χ_rep, v> = 0" for the character
    χ_rep ∈ Ĝ_odd specified by orbit_rep_g_odd, lifted to G.

    Returns
    -------
    np.ndarray of shape (r, |G|) where r = |Frobenius-orbit of χ_rep|.
        Each row is an F_2-linear constraint on the |G|-dim coordinate
        space (column j corresponds to G's j-th element under
        row-major enumeration). The kernel of this matrix over F_2
        is exactly the subspace of F_2^|G| on which χ_rep evaluates
        to zero.

    Notes
    -----
    Adapted from `_evaluate_char_sum_on_g_odd` in
    `algebraic_features.py`. The character χ_rep maps G to F_{2^r}
    (where r is the order of 2 mod the character's order); we
    represent each value as an F_2-vector of length r. The constraint
    "χ_rep(v) = 0" is then r-many F_2 constraints, one per F_2 basis
    coordinate of F_{2^r}.

    For a Frobenius orbit O of size r, all r characters in O give the
    same r-dimensional kernel constraint (since they're Galois conjugates
    of each other), so we use any single representative.
    """
    n_odds = _g_odd_orders(G)
    k_odd = orbit_rep_g_odd
    d = _chi_order_in_g_odd(k_odd, n_odds)
    r = _order_2_mod(d)
    if r not in _PRIM_POLYS:
        raise NotImplementedError(
            f"primitive polynomial of degree {r} not in table; extend _PRIM_POLYS"
        )
    p = _PRIM_POLYS[r]

    # alpha = primitive d-th root in F_{2^r}
    if d > 1 and r > 1:
        X = [0] * r
        X[1] = 1
        alpha = _fld_pow(X, (2 ** r - 1) // d, p)
    else:
        alpha = [0] * r
        alpha[0] = 1

    # alpha^j for j ∈ Z/d
    alpha_powers = [[0] * r for _ in range(d)]
    alpha_powers[0][0] = 1
    cur = alpha_powers[0][:]
    for j in range(1, d):
        cur = _fld_mul(cur, alpha, p)
        alpha_powers[j] = cur[:]

    # reduced axis exponents (matches _evaluate_char_sum_on_g_odd's convention)
    k_red: list[int] = []
    d_axes: list[int] = []
    for axis in range(G.rank):
        ka = k_odd[axis]
        no = n_odds[axis]
        if ka == 0:
            d_axes.append(1)
            k_red.append(0)
        else:
            ga = gcd(ka, no)
            d_axes.append(no // ga)
            k_red.append(ka // ga)

    # For each g in G (row-major), compute χ(g) ∈ F_2^r and lay out as
    # r F_2-rows: row i, column j = i-th F_2 coordinate of χ(g_j).
    n_G = G.cardinality
    rows = np.zeros((r, n_G), dtype=np.uint8)
    for j, g in enumerate(G):
        exp_total = 0
        for axis in range(G.rank):
            g_axis_odd = g[axis] % n_odds[axis]
            exp_total += k_red[axis] * g_axis_odd * (d // d_axes[axis])
        exp_total %= d
        chi_val = alpha_powers[exp_total]
        for i in range(r):
            rows[i, j] = chi_val[i]
    return rows


# ---------------------------------------------------------------------------
# Per-orbit dual distance
# ---------------------------------------------------------------------------


def per_orbit_dual_distance(
    poly: Poly,
    G: AbelianGroup | None = None,
    *,
    max_kernel_dim: int = 22,
) -> dict[frozenset[tuple[int, ...]], int]:
    """For each Frobenius orbit on G_odd where `poly` vanishes, return
    the minimum non-zero Hamming weight of any vector in the O-isotypic
    component of `ker(M_poly)`.

    Mathematical setup
    ------------------

    For a polynomial `A ∈ F_2[G]` and a Frobenius orbit `O` on `G_odd ≅
    Ĝ_odd`, the **O-isotypic component** of `ker(M_A)` is

        (ker M_A)_O := { v ∈ ker(M_A) : χ̂(v) = 0 ∀χ ∉ O }

    where χ̂(v) = Σ_g v(g) χ(g) ∈ F̄_2 is the Fourier coefficient. In
    the semisimple case (|G| odd), the kernel decomposes as

        ker(M_A) = ⊕_O (ker M_A)_O

    over orbits O where `A` vanishes; (ker M_A)_O = {0} for orbits
    where A doesn't vanish (since A acts as a unit there).

    The **per-orbit dual distance** is

        d_O^⊥(A) := min { wt(v) : v ∈ (ker M_A)_O \\ {0} }.

    Properties:
        * `d_O^⊥(A)` is a weight invariant of the subspace `(ker M_A)_O`.
        * `d_A^⊥ = min_wt_ker_A ≤ min_O d_O^⊥(A)` (inequality, NOT
          equality). The full kernel `ker(M_A)` decomposes as a DIRECT
          SUM over orbits, BUT a kernel vector `v = Σ_O v_O` can have
          weight far below `min_O |v_O|` due to cancellation across
          orbits. In particular, the dominant contribution to
          `min_wt_ker_A` often comes from cross-orbit mixed vectors,
          not from any single orbit's isotypical component.
        * `min_O d_O^⊥(A) ≥ d_A^⊥` — per-orbit dual distance is
          generally a STRICT UPPER bound on the global dual distance,
          NOT equal.
        * Equality `min_O d_O^⊥(A) = d_A^⊥` holds only when the
          minimum-weight kernel element happens to be concentrated on
          a single orbit's isotypical component.

    Implementation
    --------------

    Concretely, `(ker M_A)_O` is the F_2-kernel of the combined
    constraint matrix:
        1. M_A itself (so v ∈ ker M_A)
        2. For each orbit O' ≠ O: the F_2-linear constraints
           making χ̂_{O'}(v) = 0 (annihilate every non-O orbit).

    The minimum weight of this combined kernel is `d_O^⊥(A)`. We
    enumerate via brute force; safe up to `dim ≤ max_kernel_dim`.

    Parameters
    ----------
    poly : Poly
        Polynomial in F_2[G].
    G : AbelianGroup, optional
        Defaults to poly.group.
    max_kernel_dim : int
        Skip orbits whose isotypical kernel has F_2-dim above this
        threshold (default 22 — matches `min_weight_in_kernel`). For
        such orbits, the returned dict will not include them; the
        caller can detect missing orbits.

    Returns
    -------
    dict[frozenset[tuple[int, ...]], int]
        Mapping from G_odd orbit (a frozenset of G_odd elements) to
        the per-orbit dual distance. Orbits where A does NOT vanish
        (μ_O = 0) are not in the output (their distance is `+∞`).

        Orbits whose isotypical kernel exceeds `max_kernel_dim` are
        also not in the output (caller should detect via missing keys
        and possibly upgrade to a smarter min-distance algorithm).
    """
    if G is None:
        G = poly.group
    elif G != poly.group:
        raise ValueError("poly.group != G")

    M = circulant(poly)
    orbits = g_odd_frobenius_orbits(G)

    # Precompute character constraints for every orbit
    orbit_constraints: list[np.ndarray] = []
    for o in orbits:
        rep = next(iter(o))
        orbit_constraints.append(_char_constraint_rows_g_odd(G, rep))

    result: dict[frozenset[tuple[int, ...]], int] = {}
    for i, orbit in enumerate(orbits):
        mu = jacobson_radical_depth(poly, orbit, G)
        if mu == 0:
            # A doesn't vanish on this orbit; its isotypical kernel is {0}.
            continue
        # Build the combined constraint: M_A union with character constraints
        # of all OTHER orbits (forcing the kernel to live on orbit i only).
        rows = [M]
        for j, _ in enumerate(orbits):
            if j == i:
                continue
            rows.append(orbit_constraints[j])
        combined = np.vstack(rows).astype(np.uint8)
        ker_O = nullspace_f2(combined)
        if ker_O.shape[0] == 0:
            # Should not happen if μ > 0, but guard anyway.
            continue
        if ker_O.shape[0] > max_kernel_dim:
            # Too big to brute-force; skip.
            continue
        # Use the dense Gray-code enumeration via min_weight_in_kernel
        # — but it takes M, not basis. Reimplement minimally.
        n = ker_O.shape[1]
        best = n + 1
        acc = np.zeros(n, dtype=np.uint8)
        for mask in range(1, 1 << ker_O.shape[0]):
            toggled = (mask ^ (mask - 1)).bit_length() - 1
            acc ^= ker_O[toggled]
            w = int(acc.sum())
            if 0 < w < best:
                best = w
        result[orbit] = best
    return result


# ---------------------------------------------------------------------------
# Lin-Pryadko TZ lower bound (Statement 12)
# ---------------------------------------------------------------------------


def _support_subgroup_order(
    supp: frozenset[tuple[int, ...]], G: AbelianGroup
) -> int:
    """Order of ⟨supp⟩ ≤ G. BFS-closure under group operations."""
    orders = G.orders
    identity = tuple(0 for _ in orders)
    elements: set[tuple[int, ...]] = {identity}
    frontier: list[tuple[int, ...]] = list(supp)
    while frontier:
        nxt: list[tuple[int, ...]] = []
        for g in list(elements):
            for h in supp:
                gh = tuple((gi + hi) % oi for gi, hi, oi in zip(g, h, orders))
                gmh = tuple((gi - hi) % oi for gi, hi, oi in zip(g, h, orders))
                if gh not in elements:
                    elements.add(gh)
                    nxt.append(gh)
                if gmh not in elements:
                    elements.add(gmh)
                    nxt.append(gmh)
        frontier = nxt
    return len(elements)


def _intersection_subgroup_order(
    suppA: frozenset[tuple[int, ...]],
    suppB: frozenset[tuple[int, ...]],
    G: AbelianGroup,
) -> int:
    """Order of ⟨supp(A)⟩ ∩ ⟨supp(B)⟩ ≤ G."""
    orders = G.orders
    identity = tuple(0 for _ in orders)

    def closure(supp: frozenset[tuple[int, ...]]) -> set[tuple[int, ...]]:
        out = {identity}
        frontier = list(supp)
        while frontier:
            nxt: list[tuple[int, ...]] = []
            for g in list(out):
                for h in supp:
                    gh = tuple((gi + hi) % oi for gi, hi, oi in zip(g, h, orders))
                    gmh = tuple((gi - hi) % oi for gi, hi, oi in zip(g, h, orders))
                    if gh not in out:
                        out.add(gh)
                        nxt.append(gh)
                    if gmh not in out:
                        out.add(gmh)
                        nxt.append(gmh)
            frontier = nxt
        return out

    return len(closure(suppA) & closure(suppB))


def tz_lower_bound(A: Poly, B: Poly, G: AbelianGroup | None = None) -> int:
    """Lin-Pryadko Statement 12 / Kovalev-Pryadko Theorem 5:

        d ≥ ⌈min(d_A^⊥, d_B^⊥) / c⌉,  c = |G_a ∩ G_b|.

    All ingredients are weight invariants (d_A^⊥, d_B^⊥) and a
    structural quantity (c). The output is a lower bound on `d_X`.

    Citation: Lin-Pryadko 2023 arXiv:2306.16400 Statement 12 (§IV.F);
    equivalent to Kovalev-Pryadko 2013 arXiv:1212.6703 Theorem 5
    (modulo floor-vs-ceiling).

    Parameters
    ----------
    A, B : Poly in F_2[G].
    G : AbelianGroup, optional. Defaults to A.group.

    Returns
    -------
    int
        ⌈min(d_A^⊥, d_B^⊥) / c⌉. ≥ 1 always (capped from below by 1
        since d ≥ 1 for any non-trivial code).
    """
    if G is None:
        G = A.group
    if A.group != B.group:
        raise ValueError("A and B must live in the same group algebra")

    M_A = circulant(A)
    M_B = circulant(B)
    d_A_perp = min_weight_in_kernel(M_A)
    d_B_perp = min_weight_in_kernel(M_B)
    c = _intersection_subgroup_order(A.support, B.support, G)
    return max(1, math.ceil(min(d_A_perp, d_B_perp) / max(c, 1)))


# ---------------------------------------------------------------------------
# BCH-style per-orbit lower bound on d_A^⊥
# ---------------------------------------------------------------------------


def _cyclotomic_cosets(n: int, q: int = 2) -> list[frozenset[int]]:
    """Return the q-cyclotomic cosets mod n, sorted by smallest element.

    The i-th coset is { i · q^k mod n : k ∈ N }. For F_2 / cyclic codes,
    this is the standard decomposition.
    """
    if n == 0:
        return []
    cosets: list[frozenset[int]] = []
    seen: set[int] = set()
    for i in range(n):
        if i in seen:
            continue
        c: set[int] = set()
        cur = i
        while cur not in c:
            c.add(cur)
            cur = (cur * q) % n
        seen.update(c)
        cosets.append(frozenset(c))
    return sorted(cosets, key=lambda s: min(s))


def bch_per_orbit_lower_bound(poly: Poly, G: AbelianGroup | None = None) -> int:
    """Apply the BCH (Bose-Chaudhuri-Hocquenghem) designed-distance
    bound to lower-bound `d_A^⊥` for UNIVARIATE cyclic poly only.

    The classical BCH bound for a cyclic code of length n with
    defining set S ⊆ Z/n says: if the spectrum (zeros of the cyclic-
    code generating polynomial) contains δ-1 consecutive integers,
    the **code** has minimum distance ≥ δ.

    For a polynomial `A ∈ F_2[Z_n]` (univariate cyclic), the "spectrum"
    where A vanishes (in Ĝ ≅ Z/n) determines a classical cyclic
    code; the BCH bound applies to its dual.

    **WARNING**: the bivariate-per-axis version of this bound that
    appears in some draft literature is INCORRECT in general. For
    `A = 1 + x + x^2 ∈ F_2[Z_3 × Z_6]` (no y-dependence), the dual
    code `ker(M_A)` has min weight 2 (single y-fiber kernel
    elements), but a "per-axis BCH" over the y-axis would falsely
    claim min weight 6 (full consecutive y-zeros). This module's
    function therefore restricts to rank-1 groups; multi-axis
    cases return the trivial lower bound 1.

    NOTE (2026-06 adversarial review): the rank-1 restriction is
    *conservative* — the counterexample above is axis-degenerate
    (zero support on the y-axis), which is exactly the case a
    careful multivariate statement would exclude by hypothesis. No
    counterexample is known for polynomials with support on every
    axis; whether per-axis BCH is valid under a full-axis-support
    hypothesis is open (HANDOFF §6j "Reopened directions" item 3).
    Behavior is unchanged here pending that investigation.

    Returns a lower bound on `d_A^⊥`.

    Parameters
    ----------
    poly : Poly in F_2[G].
    G : AbelianGroup, optional.

    Returns
    -------
    int
        BCH lower bound on `d_A^⊥`. ≥ 1 always.
    """
    if G is None:
        G = poly.group
    elif G != poly.group:
        raise ValueError("poly.group != G")

    if not poly.support:
        # zero poly: kernel is all of F_2^|G|, min weight = 1.
        return 1

    # Only apply BCH on rank-1 (univariate cyclic) groups. The
    # per-axis multivariate version is wrong for "degenerate" polys
    # that have no support on some axis (see docstring caveat).
    if G.rank != 1:
        return 1

    n_axis = G.orders[0]
    axis_values = sorted({g[0] for g in poly.support})
    n = n_axis
    if n == 0:
        return 1
    complement = sorted(set(range(n)) - set(axis_values))
    if not complement:
        return 1
    if len(complement) == n:
        return 1
    # Find longest cyclic consecutive run in complement.
    complement_set = set(complement)
    longest = 0
    for start in complement_set:
        run = 0
        cur = start
        while cur in complement_set:
            run += 1
            cur = (cur + 1) % n
            if cur == start:
                break
        if run > longest:
            longest = run
    bch_lb = longest + 1
    return bch_lb


# ---------------------------------------------------------------------------
# Joint kernel minimum weight (diagnostic, upper bound on d_X)
# ---------------------------------------------------------------------------


def joint_kernel_min_weight(
    A: Poly, B: Poly, G: AbelianGroup | None = None
) -> int:
    """Compute the minimum non-zero Hamming weight of any vector in
    `ker(M_A) ∩ ker(M_B)`.

    This is a weight invariant of the joint kernel as a linear code.
    Useful diagnostically: a logical X-coset rep lives in this subspace
    (modulo the rowspan of `H_X`), so `d_X ≤ joint_kernel_min_weight`.

    **DOES NOT give a lower bound on `d_X`.** Useful for understanding
    where bounds become tight or loose.

    Parameters
    ----------
    A, B : Poly in F_2[G].
    G : AbelianGroup, optional. Defaults to A.group.

    Returns
    -------
    int
        Minimum non-zero Hamming weight of `ker(M_A) ∩ ker(M_B)`. If
        the joint kernel is trivial, returns `|G| + 1` as a sentinel.
    """
    if G is None:
        G = A.group
    if A.group != B.group:
        raise ValueError("A and B must live in the same group algebra")

    M_A = circulant(A)
    M_B = circulant(B)
    combined = np.vstack([M_A, M_B]).astype(np.uint8)
    return min_weight_in_kernel(combined)


# ---------------------------------------------------------------------------
# Aggregate convenience: per-orbit minimum dual distance
# ---------------------------------------------------------------------------


def min_per_orbit_dual_distance(
    poly: Poly,
    G: AbelianGroup | None = None,
    *,
    max_kernel_dim: int = 22,
) -> int:
    """Return `min_O d_O^⊥(A)` over the vanishing orbits.

    This is an UPPER bound on `d_A^⊥` — strictly greater in general,
    because cross-orbit cancellation can produce kernel elements of
    weight below `min_O d_O^⊥`. See `per_orbit_dual_distance` doc for
    details.

    The "min per-orbit" quantity is itself a weight invariant: each
    `d_O^⊥` is a min-weight invariant of its isotypical subspace.
    """
    pods = per_orbit_dual_distance(poly, G, max_kernel_dim=max_kernel_dim)
    if not pods:
        # No vanishing orbit; ker is trivial.
        if G is None:
            G = poly.group
        return G.cardinality + 1
    return min(pods.values())


def max_per_orbit_dual_distance(
    poly: Poly,
    G: AbelianGroup | None = None,
    *,
    max_kernel_dim: int = 22,
) -> int:
    """Return `max_O d_O^⊥(A)` over the vanishing orbits.

    A high `max_per_orbit_dual_distance` means at least one isotypical
    component has heavy "covering" kernel — relevant to where logical
    operators concentrate.

    For diagnostic use; CAN be on the RHS of a candidate of the form
    "d_X ≥ max_O d_O^⊥(A) / c'" if combined with appropriate denominators.
    """
    pods = per_orbit_dual_distance(poly, G, max_kernel_dim=max_kernel_dim)
    if not pods:
        if G is None:
            G = poly.group
        return G.cardinality + 1
    return max(pods.values())


def joint_per_orbit_dual_distance(
    A: Poly, B: Poly, G: AbelianGroup | None = None, *, max_kernel_dim: int = 22,
) -> dict[frozenset[tuple[int, ...]], int]:
    """For each Frobenius orbit where BOTH A and B vanish, return the
    minimum non-zero Hamming weight of any vector in the O-isotypic
    component of `ker(M_A) ∩ ker(M_B)`.

    This is the **joint** per-orbit dual distance — a weight invariant
    of the joint kernel restricted to each orbit's component.

    For orbits where one or both polynomials don't vanish, the joint
    kernel's O-component is trivial.
    """
    if G is None:
        G = A.group
    if A.group != B.group:
        raise ValueError("A and B must live in the same group algebra")

    M_A = circulant(A)
    M_B = circulant(B)
    orbits = g_odd_frobenius_orbits(G)
    orbit_constraints: list[np.ndarray] = []
    for o in orbits:
        rep = next(iter(o))
        orbit_constraints.append(_char_constraint_rows_g_odd(G, rep))

    result: dict[frozenset[tuple[int, ...]], int] = {}
    for i, orbit in enumerate(orbits):
        mu_A = jacobson_radical_depth(A, orbit, G)
        mu_B = jacobson_radical_depth(B, orbit, G)
        if mu_A == 0 or mu_B == 0:
            continue
        rows = [M_A, M_B]
        for j, _ in enumerate(orbits):
            if j == i:
                continue
            rows.append(orbit_constraints[j])
        combined = np.vstack(rows).astype(np.uint8)
        ker_joint_O = nullspace_f2(combined)
        if ker_joint_O.shape[0] == 0:
            continue
        if ker_joint_O.shape[0] > max_kernel_dim:
            continue
        n = ker_joint_O.shape[1]
        best = n + 1
        acc = np.zeros(n, dtype=np.uint8)
        for mask in range(1, 1 << ker_joint_O.shape[0]):
            toggled = (mask ^ (mask - 1)).bit_length() - 1
            acc ^= ker_joint_O[toggled]
            w = int(acc.sum())
            if 0 < w < best:
                best = w
        result[orbit] = best
    return result
