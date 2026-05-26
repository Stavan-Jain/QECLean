"""Algebraic-decomposition features of F_2[G] for BB codes.

For a finite abelian group `G` and polynomial `A ∈ F_2[G]`, the **Frobenius
orbits on the character group Ĝ** capture the algebraic decomposition of
A into its "Fourier components" over F̄_2 (the algebraic closure of F_2).

Math summary
------------

For G abelian with `|G|` coprime to 2, Maschke / Wedderburn gives

    F_2[G]  ≅  ∏_{O ∈ Ĝ // Frobenius}  F_{2^|O|},

one finite-field factor per Frobenius orbit on Ĝ ≅ G. Frobenius acts on
Ĝ by squaring, equivalently k ↦ 2k coordinate-wise on G ≅ Ĝ. Each orbit
O has size r = |O| = ord_d(2) where d = order of the orbit's representative
in Ĝ. The corresponding finite field is F_{2^r}.

A polynomial `A ∈ F_2[G]` decomposes as `(A_O)_O` and `A vanishes on O`
means `A_O = 0` in F_{2^|O|}. Equivalently, `A` lies in the ideal
`Ann(O) ⊂ F_2[G]` annihilating the O-component. For odd `|G|`, the
formula `dim ker(M_A) = Σ_O |O| · [A vanishes on O]` (sum of orbit sizes
weighted by vanishing) recovers the full kernel dimension.

For `|G|` not coprime to 2 (e.g. the gross code `G = Z_12 × Z_6`), F_2[G]
is **not semisimple** — it has a Jacobson radical (nilpotents) coming
from the 2-Sylow part. Characters of even order do not lift to F̄_2.
The "Frobenius orbits on Ĝ" picture only captures the **semisimple
quotient** of F_2[G], which is `F_2[G/G[2-Sylow]] = F_2[G_odd]`. The
formula `dim ker = Σ |O| · [vanishing]` then captures the kernel dim
**in the semisimple quotient** only; the radical contributes additional
dimension beyond what orbit-vanishing sees. We document this discrepancy
explicitly and present the orbit/vanishing structure as defined for
G_odd, lifted to G.

References
----------

This is textbook character theory of finite abelian groups over F_p (see
e.g. Lidl & Niederreiter, *Finite Fields*, Ch. 6; Curtis & Reiner,
*Methods of Representation Theory* Vol. 1, Ch. 1). Cyclotomic-coset
factorization of x^n - 1 over F_p is standard in classical coding theory
(e.g. MacWilliams & Sloane, *Theory of Error-Correcting Codes*, Ch. 7).
The Mattson-Solomon transform is the analog of the DFT in this setting.

What's "new" here is just the application: computing per-orbit vanishing
signatures across the BB-code corpus to look for predictors of distance
tightness. The orbit and vanishing constructions themselves are not.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd, lcm
from typing import Sequence

from .group import AbelianGroup
from .poly import Poly


# ---------------------------------------------------------------------------
# Finite-field arithmetic in F_{2^r} = F_2[X]/(p(X)) for a primitive p
# ---------------------------------------------------------------------------

# Primitive polynomials over F_2 for small degree r. Each is the
# lex-smallest primitive polynomial of its degree (standard tables;
# see e.g. Lin & Costello, *Error Control Coding*, Appendix C).
# The polynomial is stored as [c_0, c_1, ..., c_r] in F_2.
_PRIM_POLYS: dict[int, list[int]] = {
    1: [1, 1],                                # t + 1
    2: [1, 1, 1],                             # t^2 + t + 1
    3: [1, 1, 0, 1],                          # t^3 + t + 1
    4: [1, 1, 0, 0, 1],                       # t^4 + t + 1
    5: [1, 0, 1, 0, 0, 1],                    # t^5 + t^2 + 1
    6: [1, 1, 0, 0, 0, 0, 1],                 # t^6 + t + 1
    7: [1, 1, 0, 0, 0, 0, 0, 1],              # t^7 + t + 1
    8: [1, 0, 1, 1, 1, 0, 0, 0, 1],           # t^8 + t^4 + t^3 + t^2 + 1
    9: [1, 0, 0, 0, 1, 0, 0, 0, 0, 1],        # t^9 + t^4 + 1
    10: [1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1],    # t^10 + t^3 + 1
    11: [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], # t^11 + t^2 + 1
    12: [1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1],  # t^12 + t^6 + t^4 + t + 1
}


def _fld_mul(a: list[int], b: list[int], p: list[int]) -> list[int]:
    """Multiply two F_{2^r} elements (as F_2-vectors of length r) modulo
    the primitive polynomial p (of degree r)."""
    r = len(a)
    # Schoolbook multiplication over F_2
    result = [0] * (2 * r - 1)
    for i in range(r):
        if a[i]:
            for j in range(r):
                if b[j]:
                    result[i + j] ^= 1
    # Reduce result (degree up to 2r-2) modulo p (degree r)
    for d in range(len(result) - 1, r - 1, -1):
        if result[d]:
            shift = d - r
            for i in range(r + 1):
                result[i + shift] ^= p[i]
    return result[:r]


def _fld_pow(a: list[int], n: int, p: list[int]) -> list[int]:
    """Compute a^n in F_{2^r} via square-and-multiply."""
    r = len(a)
    result = [0] * r
    result[0] = 1  # multiplicative identity
    if n == 0:
        return result
    base = a[:]
    while n > 0:
        if n & 1:
            result = _fld_mul(result, base, p)
        n >>= 1
        if n > 0:
            base = _fld_mul(base, base, p)
    return result


def _order_2_mod(d: int) -> int:
    """Smallest r > 0 with 2^r ≡ 1 (mod d). Special case d = 1 returns 1."""
    if d == 1:
        return 1
    if d % 2 == 0:
        raise ValueError(
            f"_order_2_mod({d}): expected odd d (so that 2 is a unit "
            "in Z/d). Even d means the character doesn't lift to F̄_2."
        )
    r = 1
    x = 2 % d
    while x != 1:
        r += 1
        x = (x * 2) % d
        if r > 64:
            raise RuntimeError(f"_order_2_mod({d}): order exceeds 64")
    return r


# ---------------------------------------------------------------------------
# Odd-order quotient of an abelian group
# ---------------------------------------------------------------------------


def _odd_part(n: int) -> int:
    """Largest odd divisor of n."""
    while n % 2 == 0:
        n //= 2
    return n if n else 1


def _g_odd_orders(G: AbelianGroup) -> tuple[int, ...]:
    """Per-axis orders of the maximal odd-quotient G_odd of G.

    For G = Z_{n_1} × ... × Z_{n_d}, G_odd is the quotient by the
    2-Sylow subgroup, isomorphic to Z_{n_1_odd} × ... × Z_{n_d_odd}
    where n_axis_odd = largest odd divisor of n_axis.
    """
    return tuple(_odd_part(n) for n in G.orders)


def _project_to_g_odd(k: tuple[int, ...], G: AbelianGroup) -> tuple[int, ...]:
    """Project k ∈ G to k_odd ∈ G_odd (per-axis mod by axis odd part).

    Concretely: each axis has n_axis = 2^a · n_odd; the projection
    Z_{n_axis} → Z_{n_odd} is g ↦ g mod n_odd (since Z_{n_axis} ≅
    Z_{2^a} × Z_{n_odd} via CRT when gcd(2^a, n_odd) = 1).
    """
    n_odds = _g_odd_orders(G)
    return tuple(ki % no for ki, no in zip(k, n_odds))


# ---------------------------------------------------------------------------
# Frobenius orbits on G
# ---------------------------------------------------------------------------


def frobenius_orbits(G: AbelianGroup) -> list[frozenset[tuple[int, ...]]]:
    """Enumerate Frobenius orbits of `g ↦ 2g` on G.

    Returns a list of frozensets partitioning G. Sizes sum to `|G|`.

    For `|G|` odd (= gcd(|G|, 2) = 1), the map `g ↦ 2g` is bijective and
    these are standard group-theoretic orbits — the orbits on the
    character group Ĝ ≅ G under Frobenius squaring. The number of
    orbits equals the number of irreducible factor components of F_2[G]
    (the Wedderburn decomposition).

    For `|G|` even, `g ↦ 2g` is no longer injective: pre-cycle elements
    appear as singleton orbits because they cannot be reached by
    iterating from any other element. The partition is well-defined
    (each element belongs to a unique "iterate-from-unvisited" class)
    but the algebraic interpretation as character orbits over F̄_2 only
    applies cleanly to the semisimple quotient F_2[G_odd] (see module
    docstring).

    Determinism: orbits are returned in the order their representatives
    are encountered by `iter(G)` (row-major), with each orbit listed as
    a frozenset. Use `sorted(orbits, key=lambda o: (len(o), sorted(o)))`
    if a canonical order is needed downstream.
    """
    seen: set[tuple[int, ...]] = set()
    orbits: list[frozenset[tuple[int, ...]]] = []
    for g in G:
        if g in seen:
            continue
        chain: list[tuple[int, ...]] = []
        cur = g
        while cur not in seen:
            seen.add(cur)
            chain.append(cur)
            cur = G.add(cur, cur)  # 2·cur
        orbits.append(frozenset(chain))
    # Sanity: orbits partition G.
    assert sum(len(o) for o in orbits) == G.cardinality, (
        f"orbit sizes sum to {sum(len(o) for o in orbits)}, expected {G.cardinality}"
    )
    return orbits


# ---------------------------------------------------------------------------
# Character order and evaluation in F̄_2
# ---------------------------------------------------------------------------


def _chi_order_in_g_odd(k_odd: tuple[int, ...], n_odds: tuple[int, ...]) -> int:
    """Order of the character χ_{k_odd} on G_odd.

    For G_odd = Z_{n_1_odd} × ..., the order of χ_k is
    lcm_axes(n_axis_odd / gcd(k_axis, n_axis_odd)).
    """
    if all(ki == 0 for ki in k_odd):
        return 1
    d = 1
    for ki, ni in zip(k_odd, n_odds):
        if ki == 0:
            d_axis = 1
        else:
            d_axis = ni // gcd(ki, ni)
        d = lcm(d, d_axis)
    return d


def _evaluate_char_sum_on_g_odd(
    A: Poly, G: AbelianGroup, k: tuple[int, ...]
) -> list[int]:
    """Compute Â(χ_{k_odd}) ∈ F̄_2 where k_odd is the projection of k to G_odd.

    Specifically, the character χ_{k_odd} of G_odd is lifted to G via the
    canonical surjection G → G_odd; then

        Â(χ_{k_odd}) = Σ_{g ∈ G} A(g) · χ_{k_odd}(g mod G_odd)
                     = Σ_{h ∈ G_odd} A_odd(h) · χ_{k_odd}(h),

    where `A_odd(h)` is the fiber-sum (mod 2) of A over the preimage of h.

    Returns the value as an F_2-vector of length r = ord_d(2), where
    d = order of χ_{k_odd}. The value is 0 iff Â = 0 in F_{2^r}.

    Implementation: build F_{2^r} = F_2[X]/(p(X)) with p a primitive
    polynomial. Take α = X^{(2^r - 1)/d} so α has multiplicative order
    exactly d, hence is a primitive d-th root of unity in F_{2^r}.
    Then evaluate the sum.
    """
    n_odds = _g_odd_orders(G)
    k_odd = _project_to_g_odd(k, G)
    d = _chi_order_in_g_odd(k_odd, n_odds)
    r = _order_2_mod(d)
    if r not in _PRIM_POLYS:
        raise NotImplementedError(
            f"primitive polynomial of degree {r} not in the small-degree "
            "table. Extend _PRIM_POLYS or compute on the fly."
        )
    p = _PRIM_POLYS[r]

    if d == 1:
        # Trivial character: Â = Σ_g A(g) = weight(A) mod 2.
        return [len(A.support) % 2]

    # α := X^{(2^r - 1)/d} ∈ F_{2^r} has multiplicative order exactly d.
    X = [0] * r
    X[1] = 1
    alpha = _fld_pow(X, (2**r - 1) // d, p)

    # Precompute α^j for j ∈ Z/d.
    alpha_powers: list[list[int]] = [[0] * r for _ in range(d)]
    alpha_powers[0][0] = 1
    cur = alpha_powers[0][:]
    for j in range(1, d):
        cur = _fld_mul(cur, alpha, p)
        alpha_powers[j] = cur[:]

    # For evaluation: χ_{k_odd}(g) = ζ_d^{exp_g} where exp_g is the
    # integer-Z reduction of the axis sums, normalized into Z/d.
    # Compute axis-wise "reduced" k_axis (= k_axis / gcd) and "axis order" d_axis.
    k_red: list[int] = []
    d_axes: list[int] = []
    for axis in range(G.rank):
        ka = k_odd[axis]
        no = n_odds[axis]
        if ka == 0:
            d_axis = 1
            k_red.append(0)
        else:
            ga = gcd(ka, no)
            d_axis = no // ga
            k_red.append(ka // ga)
        d_axes.append(d_axis)
    # Sanity: lcm of d_axes equals d
    d_check = 1
    for da in d_axes:
        d_check = lcm(d_check, da)
    assert d_check == d, f"d_axes lcm {d_check} != character order {d}"

    # Accumulate the F_2-vector sum.
    result = [0] * r
    for g in A.support:
        exp_total = 0
        for axis in range(G.rank):
            # Axis contribution: k_red[axis] · (g[axis] mod n_axis_odd) · (d / d_axes[axis]).
            # We use g[axis] mod n_axis_odd (the projection of g to G_odd's axis).
            g_axis_odd = g[axis] % n_odds[axis]
            exp_total += k_red[axis] * g_axis_odd * (d // d_axes[axis])
        exp_total %= d
        a_pow = alpha_powers[exp_total]
        for i in range(r):
            result[i] ^= a_pow[i]
    return result


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------


def vanishing_orbits(
    poly: Poly,
    G: AbelianGroup | None = None,
    orbits: Sequence[frozenset[tuple[int, ...]]] | None = None,
) -> frozenset[int]:
    """Return the set of orbit indices on which `poly` vanishes.

    "Vanishing on orbit O" means `Â(χ_{k_odd}) = 0` in F̄_2, where k_odd
    is the projection of any orbit representative k ∈ O to the
    maximal-odd quotient G_odd, and χ_{k_odd} is the corresponding
    F̄_2-character (lifted to G via the canonical surjection).

    For odd `|G|` the projection is trivial (G = G_odd), the characters
    are the standard Ĝ ≅ G characters, and `dim ker(M_A) = Σ_O |O| ·
    [vanishing]` holds exactly.

    For even `|G|`, the projection is non-trivial. Multiple G-orbits
    can share the same G_odd-projection and hence the same vanishing
    verdict. The dim-ker formula above then captures only the
    semisimple quotient kernel, not the full ker(M_A); the radical of
    F_2[G] contributes additional dimension that this feature does not
    see. See `notes/T2.2_algebraic_features.md` for an example
    (the gross code).

    Parameters
    ----------
    poly : Poly
        Polynomial in F_2[G] to test.
    G : AbelianGroup, optional
        The group; defaults to `poly.group`.
    orbits : sequence of frozenset of tuples, optional
        Pre-computed orbits (use to share across multiple calls).
        Defaults to `frobenius_orbits(G)`.

    Returns
    -------
    frozenset[int]
        Indices `i` (into `orbits`) where `poly` vanishes on the i-th orbit.
    """
    if G is None:
        G = poly.group
    elif G != poly.group:
        raise ValueError("poly.group != G")
    if orbits is None:
        orbits = frobenius_orbits(G)
    vanishing: set[int] = set()
    for i, orb in enumerate(orbits):
        # Pick any representative; all reps in an orbit give the same verdict.
        rep = next(iter(orb))
        val = _evaluate_char_sum_on_g_odd(poly, G, rep)
        if all(v == 0 for v in val):
            vanishing.add(i)
    return frozenset(vanishing)


def n_vanishing_orbits(
    poly: Poly,
    G: AbelianGroup | None = None,
    orbits: Sequence[frozenset[tuple[int, ...]]] | None = None,
) -> int:
    """Return the number of orbits on which `poly` vanishes (cardinality
    of `vanishing_orbits`)."""
    return len(vanishing_orbits(poly, G, orbits))


def joint_vanishing_orbits(
    A: Poly,
    B: Poly,
    G: AbelianGroup | None = None,
    orbits: Sequence[frozenset[tuple[int, ...]]] | None = None,
) -> frozenset[int]:
    """Return orbits where both `A` and `B` vanish.

    Corresponds to `ker(M_A) ∩ ker(M_B)` in the semisimple quotient of
    F_2[G] — the "source" of nontrivial logical operators that survive
    both check matrices' annihilation.
    """
    if G is None:
        G = A.group
    if A.group != B.group:
        raise ValueError("A and B must live in the same group algebra")
    if orbits is None:
        orbits = frobenius_orbits(G)
    return vanishing_orbits(A, G, orbits) & vanishing_orbits(B, G, orbits)


def vanishing_pattern_signature(
    poly: Poly,
    G: AbelianGroup | None = None,
    orbits: Sequence[frozenset[tuple[int, ...]]] | None = None,
) -> tuple[int, ...]:
    """Compact discrete feature: the sorted tuple of orbit sizes on which
    `poly` vanishes.

    Two polynomials with the same vanishing signature have the same
    semisimple-quotient "vanishing footprint" (which finite-field
    components of F_2[G_odd] they annihilate). This is a coarse but
    hashable feature for grouping codes by their algebraic behavior.

    Example
    -------
    For the [[30,4,6]] champion (`A = 1 + x + x^2*y` on `Z_3 × Z_5`),
    `vanishing_pattern_signature(A)` is `(2,)` — A vanishes on the
    single size-2 orbit corresponding to χ_{(1, 0)} (the "x"-only
    nontrivial character).
    """
    if G is None:
        G = poly.group
    if orbits is None:
        orbits = frobenius_orbits(G)
    vs = vanishing_orbits(poly, G, orbits)
    return tuple(sorted(len(orbits[i]) for i in vs))


# ---------------------------------------------------------------------------
# Compatibility / convenience accessors
# ---------------------------------------------------------------------------


def orbit_sizes(orbits: Sequence[frozenset[tuple[int, ...]]]) -> tuple[int, ...]:
    """Sorted tuple of orbit sizes — a `G`-invariant fingerprint of the
    Frobenius orbit structure."""
    return tuple(sorted(len(o) for o in orbits))


# ---------------------------------------------------------------------------
# Jacobson-radical filtration depth μ_O(A)  (added in T3.1)
# ---------------------------------------------------------------------------
#
# The "vanishing" predicate above is binary: an orbit either lies in the
# kernel of A's projection or it doesn't. For non-semisimple F_2[G] (e.g.
# the gross-code group Z_12 × Z_6), this is too coarse: it misses the
# **multiplicity** of vanishing in the radical-filtration sense.
#
# Mathematical setup. Decompose F_2[G] = ∏_O R_O where O ranges over
# Frobenius orbits on the character group of G_odd (= G / 2-Sylow), and
# R_O = F_{2^|O|}[G_2] is the local ring at orbit O (with residue field
# F_{2^|O|}, radical the augmentation ideal of F_{2^|O|}[G_2]). For odd
# |G| this is the classical Wedderburn decomposition; for even |G| the
# G_2 factor introduces nilpotents.
#
# Operational definition (used here).
#
#     μ_O(A) := dim_{F_{2^|O|}} ker (mult_{a_O} : R_O → R_O)
#
# where a_O is the projection of A to R_O. This is the "length" of R_O
# as an R_O-module under multiplication by a_O — a basic linear-algebra
# invariant of a_O ∈ R_O.
#
# Properties.
#   * μ_O(A) = 0  ⟺  a_O is a unit (≠ 0 in residue field) ⟺ A
#     does *not* vanish semisimply on O.
#   * μ_O(A) ≥ 1  ⟺  a_O ∈ rad R_O ⟺  A *does* vanish on O.
#   * For semisimple components (G_2 trivial, R_O = F_{2^|O|} a field),
#     μ_O(A) ∈ {0, 1}: 0 if a_O ≠ 0, 1 if a_O = 0 (then ker = R_O,
#     dim = 1 over F_{2^|O|}).
#   * For non-semisimple components, μ_O(A) ranges over {0, 1, ...,
#     |G_2|}, capturing the *depth* of a_O in the radical filtration.
#
# Compatibility with dim ker M_A. Since R_O decomposes F_2[G] as a
# direct sum of multiplication-respecting summands,
#
#     dim_{F_2} ker M_A = Σ_O |O| · μ_O(A)
#
# holds exactly. This is a *consequence* of the definition, not an
# extra hypothesis. It also serves as a useful sanity check.
#
# Worked examples (verified in tests/test_jacobson.py).
#   * Z_4, A = (1+x)² = 1+x²: single orbit (size 1), μ = 2.
#     a_O = (X-1)² ∈ F_2[t]/(t^4), depth in rad = 2.
#   * Gross G = Z_12 × Z_6, A = x³+y+y²: three vanishing orbits each
#     of G_odd-size 2, μ = 2 per orbit. dim ker = 3·2·2 = 12. ✓
#   * [[30,4,6]] champion G = Z_3 × Z_5 (semisimple), A = 1+x+x²·y:
#     one vanishing orbit (size 2), μ = 1.


def _two_part_orders(G: AbelianGroup) -> tuple[int, ...]:
    """Per-axis orders of the 2-Sylow of G (each axis's largest 2-power)."""
    out: list[int] = []
    for n in G.orders:
        a = 0
        nn = n
        while nn % 2 == 0:
            a += 1
            nn //= 2
        out.append(2 ** a)
    return tuple(out)


def _g_odd_group(G: AbelianGroup) -> AbelianGroup:
    """The odd quotient G_odd = G / 2-Sylow as a standalone group."""
    return AbelianGroup(_g_odd_orders(G))


def g_odd_frobenius_orbits(
    G: AbelianGroup,
) -> list[frozenset[tuple[int, ...]]]:
    """Frobenius orbits on G_odd (the character-orbit index set used by μ_O).

    These index the local-ring components of F_2[G]. Each orbit O has a
    local ring R_O = F_{2^|O|}[G_2]. Returns orbits as tuples in G_odd
    (which has its own axis orders, the odd-part of G's orders).
    """
    return frobenius_orbits(_g_odd_group(G))


def _project_poly_to_R_O(
    A: Poly,
    G: AbelianGroup,
    orbit_rep_g_odd: tuple[int, ...],
) -> tuple[dict[tuple[int, ...], list[int]], int, list[int], tuple[int, ...]]:
    """Project A to a_O ∈ R_O = F_{2^|O|}[G_2].

    Parameters
    ----------
    A : Poly in F_2[G]
    G : the ambient group
    orbit_rep_g_odd : representative of an orbit on G_odd (an element of
        the odd-quotient group; per-axis values are mod n_axis_odd).

    Returns
    -------
    (a_O_dict, r, prim_poly, n_2s)
        a_O_dict : {g_2 : F_{2^r}-element} mapping each 2-Sylow basis
            vector to the coefficient of [g_2] in a_O.
        r : the extension degree, = |O| = orbit size.
        prim_poly : primitive polynomial defining F_{2^r}.
        n_2s : the 2-part axis orders (group structure of G_2).
    """
    n_odds = _g_odd_orders(G)
    n_2s = _two_part_orders(G)
    k_odd = orbit_rep_g_odd
    d = _chi_order_in_g_odd(k_odd, n_odds)
    r = _order_2_mod(d)
    if r not in _PRIM_POLYS:
        raise NotImplementedError(
            f"primitive polynomial of degree {r} not in table; extend _PRIM_POLYS"
        )
    p = _PRIM_POLYS[r]

    # Build α ∈ F_{2^r} of multiplicative order d.
    if d > 1 and r > 1:
        X = [0] * r
        X[1] = 1
        alpha = _fld_pow(X, (2 ** r - 1) // d, p)
    else:
        alpha = [0] * r
        alpha[0] = 1  # α = 1 for trivial character

    # Powers α^0, ..., α^{d-1}.
    alpha_powers = [[0] * r for _ in range(d)]
    alpha_powers[0][0] = 1
    cur = alpha_powers[0][:]
    for j in range(1, d):
        cur = _fld_mul(cur, alpha, p)
        alpha_powers[j] = cur[:]

    # Reduced per-axis exponents (matches _evaluate_char_sum_on_g_odd).
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

    result: dict[tuple[int, ...], list[int]] = {}
    for g in A.support:
        g_2 = tuple(gi % n2 for gi, n2 in zip(g, n_2s))
        if d == 1:
            chi_val = [0] * r
            chi_val[0] = 1
        else:
            exp_total = 0
            for axis in range(G.rank):
                g_axis_odd = g[axis] % n_odds[axis]
                exp_total += k_red[axis] * g_axis_odd * (d // d_axes[axis])
            exp_total %= d
            chi_val = alpha_powers[exp_total][:]
        if g_2 in result:
            result[g_2] = [a ^ b for a, b in zip(result[g_2], chi_val)]
        else:
            result[g_2] = chi_val[:]
    return result, r, p, n_2s


def _f2r_matrix_rank(
    M: list[list[list[int]]], r: int, p: list[int]
) -> int:
    """F_{2^r}-rank of a matrix whose entries are F_{2^r}-elements
    (each entry a length-r list of {0,1} representing an element of
    F_2[X]/(p(X)) in the X-basis).

    In-place Gaussian elimination over F_{2^r}.
    """
    # Copy to avoid aliasing the caller's matrix.
    M = [[entry[:] for entry in row] for row in M]
    rows = len(M)
    cols = len(M[0]) if rows > 0 else 0
    pivot_row = 0
    for col in range(cols):
        if pivot_row >= rows:
            break
        # Find a row with non-zero entry at `col` in [pivot_row, rows)
        pivot_idx = -1
        for i in range(pivot_row, rows):
            if any(c != 0 for c in M[i][col]):
                pivot_idx = i
                break
        if pivot_idx < 0:
            continue
        if pivot_idx != pivot_row:
            M[pivot_row], M[pivot_idx] = M[pivot_idx], M[pivot_row]
        # Compute inverse of pivot via α^(2^r - 2) (Fermat in F_{2^r}*).
        pivot_elem = M[pivot_row][col]
        inv = _fld_pow(pivot_elem, 2 ** r - 2, p)
        # Normalize pivot row.
        for k in range(col, cols):
            M[pivot_row][k] = _fld_mul(M[pivot_row][k], inv, p)
        # Eliminate all other rows.
        for i in range(rows):
            if i == pivot_row:
                continue
            if not any(c != 0 for c in M[i][col]):
                continue
            factor = M[i][col][:]
            for k in range(col, cols):
                term = _fld_mul(factor, M[pivot_row][k], p)
                M[i][k] = [a ^ b for a, b in zip(M[i][k], term)]
        pivot_row += 1
    return pivot_row


def jacobson_radical_depth(
    poly: Poly,
    orbit: frozenset[tuple[int, ...]],
    G: AbelianGroup | None = None,
) -> int:
    """Return μ_O(poly) := dim_{F_{2^|O|}} ker(mult_a_O : R_O → R_O).

    Parameters
    ----------
    poly : Poly
        A polynomial in F_2[G].
    orbit : frozenset of tuples
        A Frobenius orbit on **G_odd** (NOT G). Use
        `g_odd_frobenius_orbits(G)` to enumerate the relevant orbits.
        Each tuple's per-axis values are in G_odd's axis ranges.
    G : AbelianGroup, optional
        Defaults to `poly.group`.

    Returns
    -------
    int
        μ_O(poly). Convention:
          * 0  if poly does not vanish on O (image is a unit).
          * ≥ 1 if poly vanishes on O. For semisimple O (G_2 trivial),
            μ ∈ {0, 1}. For non-semisimple O, μ ranges up to |G_2|.
          * |G_2| (= max possible) when the projection a_O is the zero
            element of R_O (i.e., poly's O-isotypic part is identically
            zero — kernel is all of R_O).

    Examples
    --------
    Gross, A = x³+y+y², orbit = {(1,1), (2,2)} ∈ Frobenius(G_odd=Z_3×Z_3):
        μ = 2  (a_O ∈ rad \\ rad², dim ker over F_4 = 2).
    Z_4, A = (1+x)²:
        single orbit {(0,)}, μ = 2  (a_O = t², dim ker over F_2 = 2).
    [[30,4,6]] champion, A = 1+x+x²·y, orbit = {(1,0), (2,0)}:
        μ = 1  (semisimple, a_O = 0 in F_4 = R_O).
    """
    if G is None:
        G = poly.group
    elif G != poly.group:
        raise ValueError("poly.group != G")
    rep = next(iter(orbit))

    # Sanity: orbit elements should live in G_odd, not G. Validate the
    # representative by checking each axis is in G_odd's range.
    n_odds = _g_odd_orders(G)
    if len(rep) != G.rank:
        raise ValueError(
            f"orbit element {rep} has rank {len(rep)}, expected G.rank = {G.rank}"
        )
    for axis, (val, nod) in enumerate(zip(rep, n_odds)):
        if not 0 <= val < nod:
            raise ValueError(
                f"orbit element {rep} axis {axis} value {val} outside "
                f"G_odd's axis range [0, {nod}); did you pass an orbit on G "
                "instead of on G_odd? Use g_odd_frobenius_orbits(G)."
            )

    a_dict, r, prim_poly, n_2s = _project_poly_to_R_O(poly, G, rep)

    # |G_2|.
    G2_size = 1
    for n in n_2s:
        G2_size *= n

    if not a_dict or all(all(c == 0 for c in v) for v in a_dict.values()):
        # a_O = 0; entire R_O annihilates.
        return G2_size

    # Enumerate G_2 basis: row-major index.
    def g2_to_index(g: tuple[int, ...]) -> int:
        idx = 0
        for gi, ni in zip(g, n_2s):
            idx = idx * ni + gi
        return idx

    def index_to_g2(i: int) -> tuple[int, ...]:
        out: list[int] = []
        for ni in reversed(n_2s):
            out.append(i % ni)
            i //= ni
        return tuple(reversed(out))

    # Build the matrix of mult_a_O in the [g_2] basis. Column j is
    # a_O · [b_j] expressed as an F_{2^r}-vector over the basis.
    M: list[list[list[int]]] = [
        [[0] * r for _ in range(G2_size)] for _ in range(G2_size)
    ]
    for j in range(G2_size):
        bj = index_to_g2(j)
        for g_2, coef in a_dict.items():
            target = tuple(
                (bji + g2i) % ni for bji, g2i, ni in zip(bj, g_2, n_2s)
            )
            i = g2_to_index(target)
            M[i][j] = [a ^ b for a, b in zip(M[i][j], coef)]

    rank = _f2r_matrix_rank(M, r, prim_poly)
    return G2_size - rank


def jacobson_radical_bound(
    A: Poly,
    B: Poly,
    G: AbelianGroup | None = None,
) -> int:
    """Compute the conjectured lower bound on `d_X(BB(G, A, B))`:

        d_X  ≥  Σ_{O ∈ V_A ∩ V_B}  |O| · min(μ_O(A), μ_O(B))

    where the sum is over Frobenius orbits on G_odd where both A and B
    vanish (i.e., μ_O(A) > 0 AND μ_O(B) > 0), and μ_O is the Jacobson-
    radical filtration depth (`jacobson_radical_depth`).

    For BB codes with G = Z_ℓ × Z_m and polynomials A, B ∈ F_2[G].

    Examples
    --------
    Gross: G = Z_12 × Z_6, A = x³+y+y², B = y³+x+x²
        Joint vanishing on 2 orbits of size 2 each, μ = 2 per orbit.
        Bound = 2·min(2,2) + 2·min(2,2) = 8.
        (Actual d = 12; bound is loose by 4.)
    """
    if G is None:
        G = A.group
    if A.group != B.group:
        raise ValueError("A and B must live in the same group algebra")
    orbits = g_odd_frobenius_orbits(G)
    total = 0
    for orbit in orbits:
        mu_A = jacobson_radical_depth(A, orbit, G)
        mu_B = jacobson_radical_depth(B, orbit, G)
        if mu_A == 0 or mu_B == 0:
            continue
        total += len(orbit) * min(mu_A, mu_B)
    return total


@dataclass(frozen=True, slots=True)
class AlgebraicFeatures:
    """Bundle of algebraic features for a single BB polynomial.

    Returned by `compute_features(A, G)`; convenient for joint use in
    DataFrame columns or feature dicts (without modifying the existing
    `features.py` API).
    """

    n_orbits: int
    orbit_sizes: tuple[int, ...]
    vanishing_orbit_indices: frozenset[int]
    n_vanishing: int
    vanishing_signature: tuple[int, ...]


def compute_features(
    poly: Poly,
    G: AbelianGroup | None = None,
    orbits: Sequence[frozenset[tuple[int, ...]]] | None = None,
) -> AlgebraicFeatures:
    """Compute the full bundle of algebraic features for `poly`."""
    if G is None:
        G = poly.group
    if orbits is None:
        orbits = frobenius_orbits(G)
    vs = vanishing_orbits(poly, G, orbits)
    return AlgebraicFeatures(
        n_orbits=len(orbits),
        orbit_sizes=tuple(sorted(len(o) for o in orbits)),
        vanishing_orbit_indices=vs,
        n_vanishing=len(vs),
        vanishing_signature=tuple(sorted(len(orbits[i]) for i in vs)),
    )
