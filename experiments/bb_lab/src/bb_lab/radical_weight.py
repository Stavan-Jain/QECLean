"""Weight-aware Jacobson-radical filtration invariants for F_2[G] (C-v1).

For a finite abelian group `G` with `2 | |G|`, write `G = G_odd × G_2`
where `G_2` is the 2-Sylow subgroup. The group algebra factors as

    F_2[G] ≅ ⊕_O R_O,   R_O = F_{2^|O|}[G_2]

over Frobenius orbits `O` on the character group of `G_odd`. Each
`R_O` is a local ring with maximal ideal `m_O` = the augmentation
ideal of `F_{2^|O|}[G_2]`. The Loewy filtration

    R_O ⊃ m_O ⊃ m_O² ⊃ ⋯ ⊃ m_O^L = 0

has length `L = Σ_axis (2^{a_axis} − 1) + 1` for
`G_2 = ∏_axis Z_{2^{a_axis}}`.

For `A ∈ F_2[G]` and each `(O, μ)` with `μ ∈ {1, …, L}`, define

    V_{O, μ}(A) := { f ∈ R_O ⊂ F_2[G] : f · A = 0,  f ∈ m_O^{μ−1} }
    w_μ(A, O)  := min { |f|_H : f ∈ V_{O, μ}(A) \\ {0} }   (∞ if {0})

`w_μ` is a **weight invariant** (min Hamming weight over an
F_2-subspace) refining the Jacobson-radical depth `μ_O(A)` from
`algebraic_features.py` (which is a dimension invariant — falsified
for distance bounds in T2 round 1 per HANDOFF §6h).

Invariance properties (W1):
- G-translation `f ↦ g · f`: preserved.
- Aut(G) automorphisms `f ↦ σ̃(f)`: preserved (orbits permuted).
- Block-swap (A ↔ B): `w_μ` is per-polynomial.
- F_2[G]-unit multiplication: **NOT** preserved (Hamming weight not
  preserved by general unit multiplication).

Semisimple-limit recovery (W4):
- For `|G|` odd (G_2 trivial), R_O = F_{2^|O|} a field and m_O = 0.
- `w_1(A, O)` then equals `weight_invariants.per_orbit_dual_distance`
  on vanishing orbits and ∞ elsewhere.
- `w_μ(A, O) = ∞` for `μ ≥ 2` in the semisimple limit.

For non-semisimple G, `w_1(A, O)` is generally NOT equal to
`per_orbit_dual_distance(A, O)`: the latter uses a G_2-fiber-summed
character constraint, while `w_μ` uses the proper per-fiber
per-orbit constraint (correctly pinning `v` to `R_O ⊂ F_2[G]`).

See `notes/Cv1_literature.md` for prior art (Berman–Charpin–
Andriatahiny for elementary-abelian-p-group radical powers,
Jitman–Ling 2013 for non-semisimple PIGA upper bounds) and
`notes/Cv1_design.md` for the design choices.
"""

from __future__ import annotations

from itertools import product
from math import gcd

import numpy as np

from .algebraic_features import (
    _PRIM_POLYS,
    _chi_order_in_g_odd,
    _fld_mul,
    _fld_pow,
    _g_odd_orders,
    _order_2_mod,
    _two_part_orders,
    g_odd_frobenius_orbits,
)
from .checks import circulant
from .group import AbelianGroup
from .linalg import nullspace_f2
from .poly import Poly


# ---------------------------------------------------------------------------
# Character evaluation (returns F_2-vector of length r = |orbit|)
# ---------------------------------------------------------------------------


def _chi_eval_f2(
    k_odd: tuple[int, ...],
    h_odd: tuple[int, ...],
    n_odds: tuple[int, ...],
) -> list[int]:
    """Return χ_{k_odd}(h_odd) ∈ F_{2^r} as an F_2-vector of length r.

    Same conventions as `algebraic_features._evaluate_char_sum_on_g_odd`,
    but evaluated at a single G_odd element instead of summed over
    a polynomial's support.

    Parameters
    ----------
    k_odd : orbit representative in G_odd
    h_odd : element of G_odd to evaluate the character at
    n_odds : per-axis orders of G_odd
    """
    d = _chi_order_in_g_odd(k_odd, n_odds)
    r = _order_2_mod(d)
    if r not in _PRIM_POLYS:
        raise NotImplementedError(
            f"primitive polynomial of degree {r} not in table; "
            "extend `_PRIM_POLYS` in algebraic_features.py."
        )
    p = _PRIM_POLYS[r]

    if d == 1:
        # Trivial character: χ(h) = 1.
        out = [0] * r
        out[0] = 1
        return out

    if r > 1:
        X = [0] * r
        X[1] = 1
        alpha = _fld_pow(X, (2**r - 1) // d, p)
    else:
        alpha = [0] * r
        alpha[0] = 1

    k_red: list[int] = []
    d_axes: list[int] = []
    for ka, no in zip(k_odd, n_odds):
        if ka == 0:
            d_axes.append(1)
            k_red.append(0)
        else:
            ga = gcd(ka, no)
            d_axes.append(no // ga)
            k_red.append(ka // ga)

    exp_total = 0
    for axis in range(len(k_odd)):
        exp_total += k_red[axis] * h_odd[axis] * (d // d_axes[axis])
    exp_total %= d

    cur = [0] * r
    cur[0] = 1
    for _ in range(exp_total):
        cur = _fld_mul(cur, alpha, p)
    return cur


def _orbit_size_from_rep(
    rep: tuple[int, ...], n_odds: tuple[int, ...]
) -> int:
    """Return `r = |orbit of rep under Frobenius (g ↦ 2g) on G_odd|`."""
    return _order_2_mod(_chi_order_in_g_odd(rep, n_odds))


# ---------------------------------------------------------------------------
# G-element indexing helpers (row-major over `iter(G)`)
# ---------------------------------------------------------------------------


def _g_index_table(G: AbelianGroup) -> dict[tuple[int, ...], int]:
    """Return a dict mapping g ∈ G to its row-major index in `iter(G)`."""
    return {g: i for i, g in enumerate(G)}


# ---------------------------------------------------------------------------
# R_O membership constraints (proper per-G_2-fiber)
# ---------------------------------------------------------------------------


def r_o_constraint_rows(
    G: AbelianGroup,
    orbit_index: int,
    *,
    orbits: list[frozenset[tuple[int, ...]]] | None = None,
) -> np.ndarray:
    """F_2-constraint rows pinning `v ∈ F_2[G]` to lie in `R_O ⊂ F_2[G]`.

    For each Frobenius orbit `O' ≠ O` (where `O` is the orbit at
    `orbit_index`) and each `g_2 ∈ G_2`, append `|O'|` rows enforcing

        Σ_{h ∈ G_odd} (j-th F_2-coord of χ_{O' rep}(h)) · v_{(h, g_2)} = 0

    for `j ∈ [0, |O'|)`. Together these rows cut F_2[G] down to
    R_O = e_O · F_2[G] (the orbit-O isotypic component as an F_2-subspace).

    This is stronger than the G_2-fiber-summed character constraint
    used by `weight_invariants._char_constraint_rows_g_odd`: each
    fiber-row constrains exactly one `g_2`-fiber, where the existing
    helper sums over all `G_2` fibers. For semisimple G_2 (= trivial)
    the two notions coincide; for non-semisimple G_2 the per-fiber
    notion is more restrictive.

    Returns
    -------
    np.ndarray of shape (N, |G|), dtype uint8 — the stacked constraint
    rows. `N = |G_2| · Σ_{O' ≠ O} |O'|`. The kernel of the returned
    matrix is exactly R_O.
    """
    if orbits is None:
        orbits = g_odd_frobenius_orbits(G)
    if not 0 <= orbit_index < len(orbits):
        raise ValueError(
            f"orbit_index {orbit_index} out of range [0, {len(orbits)})"
        )

    n_odds = _g_odd_orders(G)
    n_2s = _two_part_orders(G)
    n_G = G.cardinality
    g_index = _g_index_table(G)

    rows: list[np.ndarray] = []
    for j, other in enumerate(orbits):
        if j == orbit_index:
            continue
        rep = next(iter(other))
        r_other = _orbit_size_from_rep(rep, n_odds)
        # For each G_2-fiber `g_2`, append r_other rows enforcing
        # the character value at this fiber to vanish.
        for g_2 in product(*(range(n) for n in n_2s)):
            row_block = np.zeros((r_other, n_G), dtype=np.uint8)
            for h_odd in product(*(range(n) for n in n_odds)):
                chi_val = _chi_eval_f2(rep, h_odd, n_odds)
                # Map (h_odd, g_2) back to G via CRT-like reconstruction.
                # Recall: G_odd has axis orders n_odds, G_2 has axis orders
                # n_2s, and G has axis orders n_odds[a] * n_2s[a] = G.orders[a].
                # The element g ∈ G with G_odd-projection h_odd and
                # G_2-projection g_2 is determined by CRT.
                g = _reconstruct_g_from_odd_and_2(h_odd, g_2, n_odds, n_2s)
                col = g_index[g]
                for i in range(r_other):
                    row_block[i, col] = chi_val[i]
            rows.append(row_block)
    if not rows:
        return np.zeros((0, n_G), dtype=np.uint8)
    return np.vstack(rows)


def _reconstruct_g_from_odd_and_2(
    h_odd: tuple[int, ...],
    g_2: tuple[int, ...],
    n_odds: tuple[int, ...],
    n_2s: tuple[int, ...],
) -> tuple[int, ...]:
    """Given G_odd-projection `h_odd` and G_2-projection `g_2`, return
    the unique `g ∈ G` (axis-wise CRT) with those projections.

    Each axis has order `n = n_odd · n_2` with `gcd(n_odd, n_2) = 1`.
    By CRT, the axis value `g_axis ∈ Z/n` is uniquely determined by
    `(g_axis mod n_odd, g_axis mod n_2)`. We solve via the standard
    Bezout-coefficient construction.
    """
    out: list[int] = []
    for h_o, g_t, n_o, n_t in zip(h_odd, g_2, n_odds, n_2s):
        n = n_o * n_t
        # Find coefficients (x_t, x_o) with x_t · n_t + x_o · n_o = 1
        # (gcd = 1 by the odd-vs-2-power split). Standard extended
        # Euclidean.
        a, b = n_t, n_o
        x_t_a, x_t_b = 1, 0
        x_o_a, x_o_b = 0, 1
        while b:
            q = a // b
            a, b = b, a - q * b
            x_t_a, x_t_b = x_t_b, x_t_a - q * x_t_b
            x_o_a, x_o_b = x_o_b, x_o_a - q * x_o_b
        # After loop, a = gcd = 1; x_t_a · n_t + x_o_a · n_o = 1.
        # By CRT, g_axis ≡ h_o (mod n_o) and ≡ g_t (mod n_t) is solved by
        #   g_axis ≡ h_o · x_t_a · n_t + g_t · x_o_a · n_o  (mod n).
        g_axis = (h_o * x_t_a * n_t + g_t * x_o_a * n_o) % n
        out.append(g_axis)
    return tuple(out)


# ---------------------------------------------------------------------------
# Loewy depth constraints (vanishing of (y, z, …)-monomials of low degree)
# ---------------------------------------------------------------------------


def _g_2_axes(n_2s: tuple[int, ...]) -> list[tuple[int, int]]:
    """Return `[(axis_idx, log2_order)]` for axes with non-trivial 2-part.

    Each axis has `n_2 = 2^a`. We only need the axes with `a ≥ 1`
    (others are trivial G_2-factors).
    """
    out: list[tuple[int, int]] = []
    for i, n in enumerate(n_2s):
        if n > 1:
            a = 0
            nn = n
            while nn > 1:
                a += 1
                nn //= 2
            out.append((i, a))
    return out


def _lucas_mod2(a: int, k: int) -> int:
    """Return C(a, k) mod 2 via Lucas: 1 iff binary digits of k ⊆ binary of a."""
    if k < 0 or k > a:
        return 0
    return 1 if (k & a) == k else 0


def loewy_depth_constraint_rows(
    G: AbelianGroup,
    orbit_index: int,
    mu: int,
    *,
    orbits: list[frozenset[tuple[int, ...]]] | None = None,
) -> np.ndarray:
    """F_2-constraint rows enforcing `v_R_O ∈ m_O^{μ−1}` for v ∈ R_O.

    `v_R_O` is the R_O-projection of v; the (y_axis)-monomial
    coefficient at multi-index `i = (i_axis)` is

        coeff_i(v_R_O)
            = Σ_{g_2 ∈ G_2 with g_2[axis] ≥ i[axis]}
                  (∏_axis Lucas(g_2[axis], i[axis])) · ε_O(v_{(·, g_2)})

    in F_{2^|O|}, where ε_O(w) := Σ_{h} χ_{O rep}(h) · w_h is the
    orbit-O character evaluation (lifted to G_odd).

    The Loewy-depth constraint "v_R_O ∈ m_O^{μ−1}" says that
    coeff_i(v_R_O) = 0 in F_{2^|O|} for every multi-index `i` with
    Σ i[axis] < μ−1. Each such (i, F_2-coord j) pair contributes one
    F_2-row.

    For `μ = 1`, no constraints (every f ∈ R_O is in m_O^0 = R_O).
    For `μ > L` (the Loewy length), all monomials are constrained,
    forcing v_R_O = 0 (V_{O, μ} collapses to {0}).

    Returns
    -------
    np.ndarray of shape (N, |G|), dtype uint8. `N = |O| · #monomials`
    where #monomials is the count of multi-indices `i` with
    Σ i[axis] < μ−1 (and `i[axis] < 2^{a_axis}` on each 2-Sylow axis).
    """
    if orbits is None:
        orbits = g_odd_frobenius_orbits(G)
    if mu < 1:
        raise ValueError(f"mu must be ≥ 1, got {mu}")
    if not 0 <= orbit_index < len(orbits):
        raise ValueError(
            f"orbit_index {orbit_index} out of range [0, {len(orbits)})"
        )

    n_odds = _g_odd_orders(G)
    n_2s = _two_part_orders(G)
    n_G = G.cardinality
    g_index = _g_index_table(G)

    rep = next(iter(orbits[orbit_index]))
    r = _orbit_size_from_rep(rep, n_odds)

    if mu == 1:
        # No constraints: m_O^0 = R_O.
        return np.zeros((0, n_G), dtype=np.uint8)

    threshold = mu - 1

    # Enumerate G_2 elements (as multi-indices on the full G_2 axis tuple).
    g_2_axes = _g_2_axes(n_2s)
    if not g_2_axes:
        # G_2 is trivial — no Loewy depth constraints can be defined.
        # Every monomial below threshold is forced to vanish, but the
        # only monomial is the trivial one with all i_axis = 0; its
        # coefficient is c_e = ε_O(v_(·, e)). Setting this to 0 is
        # equivalent to one F_2-row per F_2-coord of F_{2^|O|}.
        # For μ = 2: forces coeff at i = (0,...,0) to vanish.
        if mu >= 2:
            # Build the constraint: ε_O(v_{(·, identity_G_2)}) = 0.
            identity_g_2 = tuple(0 for _ in n_2s)
            row_block = np.zeros((r, n_G), dtype=np.uint8)
            for h_odd in product(*(range(n) for n in n_odds)):
                chi_val = _chi_eval_f2(rep, h_odd, n_odds)
                g = _reconstruct_g_from_odd_and_2(h_odd, identity_g_2, n_odds, n_2s)
                col = g_index[g]
                for i_coord in range(r):
                    row_block[i_coord, col] = chi_val[i_coord]
            return row_block
        return np.zeros((0, n_G), dtype=np.uint8)

    # Generate multi-indices `i` with i[axis] < 2^{a_axis} and Σ i_axis < threshold.
    # i is indexed only over the 2-Sylow axes; non-2-Sylow axes have i = 0 (trivially).
    axis_caps = [(2 ** a) for _, a in g_2_axes]
    # Enumerate all multi-indices.
    missing_multi_indices: list[tuple[int, ...]] = []
    for tup in product(*(range(cap) for cap in axis_caps)):
        if sum(tup) < threshold:
            missing_multi_indices.append(tup)

    if not missing_multi_indices:
        return np.zeros((0, n_G), dtype=np.uint8)

    # For each missing i, build |O| F_2-rows.
    rows: list[np.ndarray] = []
    for i_tup in missing_multi_indices:
        # i_tup is indexed over 2-Sylow axes only. Build the full G_2
        # multi-index (length len(n_2s)) by placing 0 on non-2-Sylow axes.
        i_full = [0] * len(n_2s)
        for slot, (axis_idx, _) in enumerate(g_2_axes):
            i_full[axis_idx] = i_tup[slot]
        i_full = tuple(i_full)

        row_block = np.zeros((r, n_G), dtype=np.uint8)
        # Sum over G_2-elements g_2 with g_2[axis] ≥ i[axis] componentwise and
        # ∏_axis Lucas(g_2[axis], i[axis]) = 1.
        for g_2 in product(*(range(n) for n in n_2s)):
            # Lucas mask across all axes.
            mask = 1
            for axis in range(len(n_2s)):
                mask &= _lucas_mod2(g_2[axis], i_full[axis])
                if not mask:
                    break
            if not mask:
                continue
            # Add the contribution Σ_h χ(h) · v_{(h, g_2)} (one F_2-row per coord).
            for h_odd in product(*(range(n) for n in n_odds)):
                chi_val = _chi_eval_f2(rep, h_odd, n_odds)
                g = _reconstruct_g_from_odd_and_2(h_odd, g_2, n_odds, n_2s)
                col = g_index[g]
                for i_coord in range(r):
                    row_block[i_coord, col] ^= chi_val[i_coord]
        rows.append(row_block)
    return np.vstack(rows)


# ---------------------------------------------------------------------------
# Min Hamming weight in an F_2-subspace via Gray-code traversal
# ---------------------------------------------------------------------------


def _min_weight_in_basis(basis: np.ndarray, max_dim: int = 22) -> int:
    """Return the minimum non-zero Hamming weight of a non-trivial F_2-
    combination of basis rows.

    Parameters
    ----------
    basis : np.ndarray of shape (k, n), dtype uint8 — k F_2-basis vectors of
        length n.
    max_dim : int — refuse to enumerate if k > max_dim (avoid blowup).

    Returns
    -------
    int — the minimum non-zero Hamming weight. If basis is empty (k=0)
    or its rowspan is trivial, returns n + 1 (a sentinel "no nonzero
    element"). Raises if k > max_dim.
    """
    k, n = basis.shape
    if k == 0:
        return n + 1
    if k > max_dim:
        raise ValueError(
            f"basis dim {k} exceeds max_dim {max_dim}; refusing to enumerate"
        )
    best = n + 1
    acc = np.zeros(n, dtype=np.uint8)
    for mask in range(1, 1 << k):
        toggled = (mask ^ (mask - 1)).bit_length() - 1
        acc ^= basis[toggled]
        w = int(acc.sum())
        if 0 < w < best:
            best = w
    return best


# ---------------------------------------------------------------------------
# Public API: w_μ(A, O), depth(O), and the gross-style table
# ---------------------------------------------------------------------------


def loewy_length(G: AbelianGroup) -> int:
    """Return the Loewy length of `R_O = F_{2^|O|}[G_2]` for any orbit O.

    The length depends only on `G_2 = ∏_axis Z_{2^{a_axis}}`:

        L = Σ_axis (2^{a_axis} − 1) + 1

    This is the nilpotency index of the augmentation ideal of `F_2[G_2]`:
    `m^{L−1} ≠ 0`, `m^L = 0`.

    For `G_2` trivial (|G| odd, semisimple case), `L = 1` — the
    radical is zero and `m^0 = R_O`, `m^1 = 0`.
    """
    n_2s = _two_part_orders(G)
    total = 0
    for n in n_2s:
        if n <= 1:
            continue
        total += n - 1
    return total + 1


def jacobson_filtration_dims(G: AbelianGroup) -> list[int]:
    """Return the F_2-dimensions of the Loewy layers `m_O^μ` for an
    arbitrary orbit `O` (the dimensions are orbit-size dependent —
    multiply by |O| to get F_2 dim).

    Specifically, returns `[dim_{F_{2^|O|}} m_O^μ]_{μ ≥ 0}` over
    `F_{2^|O|}`. The F_2-dim is then `|O| · dim_{F_{2^|O|}}`.

    For `G_2 = Z_4 × Z_2` (gross's 2-Sylow), returns
    `[8, 7, 5, 3, 1, 0]` — the augmentation-ideal-power dimensions in
    F_2[G_2].
    """
    n_2s = _two_part_orders(G)
    g_2_axes = _g_2_axes(n_2s)
    axis_caps = [(2 ** a) for _, a in g_2_axes]
    if not axis_caps:
        return [1, 0]
    L = loewy_length(G)
    dims = []
    for mu in range(L + 1):
        # Count multi-indices with Σ i_axis ≥ mu, i_axis < axis_caps[axis].
        cnt = 0
        for tup in product(*(range(cap) for cap in axis_caps)):
            if sum(tup) >= mu:
                cnt += 1
        dims.append(cnt)
    return dims


def _build_v_o_mu(
    A: Poly,
    orbit_index: int,
    mu: int,
    G: AbelianGroup,
    orbits: list[frozenset[tuple[int, ...]]],
) -> np.ndarray:
    """Build a basis of V_{O, μ}(A) as F_2-rows.

    V_{O, μ}(A) = { v ∈ F_2[G] : M_A v = 0 AND v ∈ R_O AND
                                 v_R_O ∈ m_O^{μ−1} }.

    Returns the F_2-basis (rows of the nullspace of the stacked
    constraints). Empty basis if V_{O, μ}(A) = {0}.
    """
    M_A = circulant(A)
    r_o_rows = r_o_constraint_rows(G, orbit_index, orbits=orbits)
    loewy_rows = loewy_depth_constraint_rows(G, orbit_index, mu, orbits=orbits)
    blocks = [M_A.astype(np.uint8)]
    if r_o_rows.shape[0] > 0:
        blocks.append(r_o_rows)
    if loewy_rows.shape[0] > 0:
        blocks.append(loewy_rows)
    combined = np.vstack(blocks).astype(np.uint8)
    return nullspace_f2(combined)


def w_mu(
    A: Poly,
    orbit: frozenset[tuple[int, ...]],
    mu: int,
    G: AbelianGroup | None = None,
    *,
    max_basis_dim: int = 22,
) -> int | float:
    """Compute `w_μ(A, O)` — the weight-aware Jacobson-radical filtration
    invariant.

    Parameters
    ----------
    A : Poly in F_2[G].
    orbit : frozenset[tuple[int, ...]]
        A Frobenius orbit on G_odd (use
        `algebraic_features.g_odd_frobenius_orbits(G)` to enumerate).
    mu : int
        The filtration level, `μ ≥ 1`. `μ = 1` gives the R_O-restricted
        kernel of mult by A; larger μ tightens by requiring deeper
        radical depth.
    G : AbelianGroup, optional. Defaults to A.group.
    max_basis_dim : int — refuse to enumerate min weight if the basis
        of V_{O, μ}(A) exceeds this (default 22).

    Returns
    -------
    int | float
        `w_μ(A, O)`. Returns `float('inf')` when `V_{O, μ}(A) = {0}` —
        e.g. for non-vanishing orbits, or μ exceeding the Loewy length,
        or the kernel intersection collapsing.
    """
    if G is None:
        G = A.group
    elif G != A.group:
        raise ValueError("G mismatch: A is over a different group")
    if mu < 1:
        raise ValueError(f"mu must be ≥ 1, got {mu}")

    orbits = g_odd_frobenius_orbits(G)
    try:
        orbit_index = next(i for i, o in enumerate(orbits) if o == orbit)
    except StopIteration:
        raise ValueError(
            f"orbit {orbit} not found among G_odd Frobenius orbits of {G}"
        )

    basis = _build_v_o_mu(A, orbit_index, mu, G, orbits)
    if basis.shape[0] == 0:
        return float("inf")
    if basis.shape[0] > max_basis_dim:
        raise ValueError(
            f"V_{{O,μ}}(A) basis dim {basis.shape[0]} exceeds "
            f"max_basis_dim {max_basis_dim}; tighten the constraint "
            "set or raise max_basis_dim."
        )
    best = _min_weight_in_basis(basis, max_dim=max_basis_dim)
    if best > G.cardinality:
        return float("inf")
    return best


def w_mu_table(
    A: Poly,
    G: AbelianGroup | None = None,
    *,
    max_mu: int | None = None,
    max_basis_dim: int = 22,
) -> dict[tuple[frozenset[tuple[int, ...]], int], int | float]:
    """Compute `w_μ(A, O)` over all orbits and `μ ∈ {1, …, max_mu}`.

    Parameters
    ----------
    A : Poly.
    G : AbelianGroup, optional. Defaults to A.group.
    max_mu : int, optional. Defaults to the Loewy length (so the table
        covers all non-trivial filtration levels).
    max_basis_dim : int.

    Returns
    -------
    dict[(orbit, μ) → int|inf]
        Mapping. Orbits where every μ-value is ∞ are still included
        (so the caller can see "this orbit contributes nothing" cleanly).
    """
    if G is None:
        G = A.group
    L = loewy_length(G)
    if max_mu is None:
        max_mu = L
    orbits = g_odd_frobenius_orbits(G)
    out: dict[tuple[frozenset[tuple[int, ...]], int], int | float] = {}
    for orbit in orbits:
        for mu in range(1, max_mu + 1):
            out[(orbit, mu)] = w_mu(
                A, orbit, mu, G=G, max_basis_dim=max_basis_dim
            )
    return out


# ===========================================================================
# C-v2: BB-code distance bound conjectures using w_μ
# ===========================================================================
#
# HANDOFF_C2 candidate (primary):
#
#     d_X(BB(G, A, B))  ≥  (1/c) · min_O min(w_1(A, O), w_1(B, O))
#
# where c = [G_a : G_a ∩ G_b], G_a = ⟨supp(A)⟩, G_b = ⟨supp(B)⟩, and the
# min ranges over Frobenius orbits where both w_1(A, O) and w_1(B, O)
# are finite (i.e., both polynomials vanish on O). For gross this gives
# 36/3 = 12 = d, tight.
#
# Alternative formulations are provided for A/B testing per HANDOFF_C2 §5.


def _subgroup_closure_of_support(supp, G: AbelianGroup) -> set:
    """Local copy of degeneracy._subgroup_closure to avoid the import cycle
    (radical_weight imports algebraic_features which would loop if we
    pulled degeneracy in at module level)."""
    closure = {tuple(0 for _ in G.orders)}
    if not supp:
        return closure
    frontier = set(closure)
    while frontier:
        new_frontier = set()
        for h in frontier:
            for g in supp:
                gh = G.add(h, g)
                if gh not in closure:
                    closure.add(gh)
                    new_frontier.add(gh)
        frontier = new_frontier
    return closure


def joint_support_subgroup_index(
    A: Poly, B: Poly, G: AbelianGroup | None = None
) -> int:
    """Return `c = [G_a : G_a ∩ G_b]` where `G_a = ⟨supp(A)⟩`,
    `G_b = ⟨supp(B)⟩`.

    ⚠️  **This is NOT Lin-Pryadko Statement 12's `c`.** LP Stmt 12 uses
    `c = |G_a ∩ G_b|` — the subgroup *order*, implemented in
    `weight_invariants._intersection_subgroup_order` / `tz_lower_bound`.
    This function returns the *index*, which is a categorically different
    quantity and gives a different bound shape. The C-v2 series
    (`bb_radical_bound`, Cv1 → Cv4 conjectures) deliberately uses the
    index per the HANDOFF_C2 design (see `notes/Cv2_literature.md` §2);
    candidates that aim to *match* LP12 must call the `weight_invariants`
    version instead.

    Concretely:
      * gross: `|G_a| = |G_b| = 24`, `|G_a ∩ G_b| = 8`,
        `[G_a : G_a ∩ G_b] = 3`.  LP12's c = 8; this function's c = 3.

    Definition: `[G_b : G_a ∩ G_b]` as well by Dedekind's identity for
    subgroup intersections (both supports' closures have the same
    intersection relative-index, since `|G_a| · |G_b| = |G_a · G_b| ·
    |G_a ∩ G_b|` for abelian subgroups).

    For non-degenerate BB codes (`G_a = G_b = G`), `c = 1`.

    For gross (`G_a = ⟨3⟩ × Z_6`, `G_b = Z_12 × ⟨3⟩`,
    `G_a ∩ G_b = ⟨3⟩ × ⟨3⟩`), `c = 3`.
    """
    if G is None:
        G = A.group
    if A.group != B.group:
        raise ValueError("A and B must live in the same group algebra")
    G_a = _subgroup_closure_of_support(A.support, G)
    G_b = _subgroup_closure_of_support(B.support, G)
    inter = G_a & G_b
    if not inter:
        # Degenerate input — both supports empty.
        return 1
    return len(G_a) // len(inter)


def _min_joint_w_mu(
    A: Poly,
    B: Poly,
    G: AbelianGroup,
    mu: int = 1,
    *,
    require_joint_vanishing: bool = True,
    max_basis_dim: int = 22,
) -> tuple[float | int, frozenset[tuple[int, ...]] | None]:
    """Return `(min_O min(w_μ(A, O), w_μ(B, O)), argmin orbit)`.

    Iterates Frobenius orbits on `Ĝ_odd`. If `require_joint_vanishing`
    is True, restricts to orbits where *both* `μ_O(A) > 0` and
    `μ_O(B) > 0` (the primary HANDOFF_C2 convention). If False, takes
    the min over all orbits where both `w_μ(A, O)` and `w_μ(B, O)`
    are finite (which for `μ = 1` is equivalent to joint-vanishing in
    practice).

    Returns `(float("inf"), None)` when no orbit qualifies (vacuous).
    """
    from .algebraic_features import jacobson_radical_depth  # local to avoid cycle

    orbits = g_odd_frobenius_orbits(G)
    best: float | int = float("inf")
    argmin: frozenset[tuple[int, ...]] | None = None
    for orbit in orbits:
        if require_joint_vanishing:
            if jacobson_radical_depth(A, orbit, G) == 0:
                continue
            if jacobson_radical_depth(B, orbit, G) == 0:
                continue
        wA = w_mu(A, orbit, mu, G, max_basis_dim=max_basis_dim)
        wB = w_mu(B, orbit, mu, G, max_basis_dim=max_basis_dim)
        if wA == float("inf") or wB == float("inf"):
            continue
        cand = min(wA, wB)
        if cand < best:
            best = cand
            argmin = orbit
    return best, argmin


def bb_radical_bound(
    A: Poly,
    B: Poly,
    G: AbelianGroup | None = None,
    *,
    max_basis_dim: int = 22,
) -> int | float:
    """C-v2 primary conjecture lower bound on `d_X(BB(G, A, B))`:

        d_X  ≥  ⌈(1/c) · min_O min(w_1(A, O), w_1(B, O))⌉

    where the min is over orbits where both A and B vanish, and
    `c = [G_a : G_a ∩ G_b]` is the joint-support index.

    Returns 0 when the bound is vacuous (no joint-vanishing orbit) so
    the caller can distinguish "vacuous" from "satisfied with bound 1".
    Otherwise returns a positive integer (ceiling of the rational).
    """
    if G is None:
        G = A.group
    if A.group != B.group:
        raise ValueError("A and B must live in the same group algebra")
    c = joint_support_subgroup_index(A, B, G)
    raw, _ = _min_joint_w_mu(
        A, B, G, mu=1, require_joint_vanishing=True,
        max_basis_dim=max_basis_dim,
    )
    if raw == float("inf"):
        return 0
    import math
    return math.ceil(raw / max(c, 1))


def bb_radical_bound_alt(
    A: Poly,
    B: Poly,
    G: AbelianGroup | None = None,
    *,
    formulation: str = "primary",
    max_basis_dim: int = 22,
) -> int | float:
    """C-v2 alternative formulations (HANDOFF_C2 §5).

    formulation:
        "primary"   — same as bb_radical_bound: ⌈(1/c) · min_O joint w_1⌉
        "any-orbit" — like primary but min over orbits where either A
                      or B vanishes (not requiring joint). Bound = 0 if
                      neither vanishes anywhere.
        "multi-mu"  — ⌈(1/c) · min_{O, μ ≤ min(μ_O(A), μ_O(B))}
                          min(w_μ(A,O), w_μ(B,O)) / μ⌉
        "sum"       — (1/c) · Σ_{O joint vanishing} min(w_1(A, O), w_1(B, O))
                      (Per HANDOFF_C2 §5 Alt-C: dead-on-arrival on gross;
                       included for completeness.)
        "geometric" — ⌈(1/c) · √(min_O w_1(A,O) · w_1(B,O))⌉
                      (Per HANDOFF_C2 §5 Alt-D.)

    Returns the bound (ceiling of an integer/rational quantity); 0 for
    vacuous bounds.
    """
    import math

    if G is None:
        G = A.group
    if A.group != B.group:
        raise ValueError("A and B must live in the same group algebra")
    c = joint_support_subgroup_index(A, B, G)

    if formulation == "primary":
        return bb_radical_bound(A, B, G, max_basis_dim=max_basis_dim)

    if formulation == "any-orbit":
        raw, _ = _min_joint_w_mu(
            A, B, G, mu=1, require_joint_vanishing=False,
            max_basis_dim=max_basis_dim,
        )
        if raw == float("inf"):
            return 0
        return math.ceil(raw / max(c, 1))

    if formulation == "multi-mu":
        from .algebraic_features import jacobson_radical_depth

        orbits = g_odd_frobenius_orbits(G)
        L = loewy_length(G)
        best: float | int = float("inf")
        for orbit in orbits:
            mu_A = jacobson_radical_depth(A, orbit, G)
            mu_B = jacobson_radical_depth(B, orbit, G)
            mu_max = min(mu_A, mu_B, L)
            if mu_max == 0:
                continue
            for mu in range(1, mu_max + 1):
                wA = w_mu(A, orbit, mu, G, max_basis_dim=max_basis_dim)
                wB = w_mu(B, orbit, mu, G, max_basis_dim=max_basis_dim)
                if wA == float("inf") or wB == float("inf"):
                    continue
                cand = min(wA, wB) / mu
                if cand < best:
                    best = cand
        if best == float("inf"):
            return 0
        return math.ceil(best / max(c, 1))

    if formulation == "sum":
        from .algebraic_features import jacobson_radical_depth

        orbits = g_odd_frobenius_orbits(G)
        total = 0.0
        any_orbit = False
        for orbit in orbits:
            if jacobson_radical_depth(A, orbit, G) == 0:
                continue
            if jacobson_radical_depth(B, orbit, G) == 0:
                continue
            wA = w_mu(A, orbit, 1, G, max_basis_dim=max_basis_dim)
            wB = w_mu(B, orbit, 1, G, max_basis_dim=max_basis_dim)
            if wA == float("inf") or wB == float("inf"):
                continue
            total += min(wA, wB)
            any_orbit = True
        if not any_orbit:
            return 0
        return math.ceil(total / max(c, 1))

    if formulation == "geometric":
        from .algebraic_features import jacobson_radical_depth

        orbits = g_odd_frobenius_orbits(G)
        best: float | int = float("inf")
        for orbit in orbits:
            if jacobson_radical_depth(A, orbit, G) == 0:
                continue
            if jacobson_radical_depth(B, orbit, G) == 0:
                continue
            wA = w_mu(A, orbit, 1, G, max_basis_dim=max_basis_dim)
            wB = w_mu(B, orbit, 1, G, max_basis_dim=max_basis_dim)
            if wA == float("inf") or wB == float("inf"):
                continue
            cand = math.sqrt(wA * wB)
            if cand < best:
                best = cand
        if best == float("inf"):
            return 0
        return math.ceil(best / max(c, 1))

    raise ValueError(
        f"unknown formulation {formulation!r}; expected one of: "
        "primary, any-orbit, multi-mu, sum, geometric"
    )
