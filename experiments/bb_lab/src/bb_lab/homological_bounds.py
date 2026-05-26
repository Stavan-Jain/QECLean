"""Cover-graph chain-map distance bound for BB codes.

This module implements the **Symons–Rajput–Browne 2025** cover-graph
chain-map distance transfer for bivariate-bicycle (BB) codes:

    B. C. B. Symons, A. Rajput, D. E. Browne.
    "Sequences of Bivariate Bicycle Codes from Covering Graphs."
    arXiv:2511.13560 (Nov 17, 2025).

The headline result the module implements
============================================

Let `Q̃(Ã, B̃, l̃, m̃)` be an h-fold cover of a base BB code
`Q(A, B, l, m)`, where `h = u · t`, `l̃ = u·l`, `m̃ = t·m`, and the
defining polynomials satisfy `π(Ã) = A`, `π(B̃) = B` under the
"mod (l, m)" projection on monomial exponents (SRB Theorem 3.1).

Then (SRB Theorem 4.6 + 4.7):

    if h is odd AND k_h = k:    d_base ≤ d_cover ≤ h · d_base.

The proof uses a projection chain map `p• : Q̃• → Q•` (SRB Theorem 4.1)
and a lifting chain map `τ• : Q• → Q̃•` (SRB Theorem 4.3) with
`p• ∘ τ• = h · I`. Over F₂, this is `I` for h odd, **0** for h even
(SRB Lemma 4.4). The chain-map injectivity argument that lifts a
non-zero base homology class to a non-zero cover class breaks for
even h.

For **even h**, SRB §7 conjectures the same bound still holds, based
on extensive numerical data:

    conj.    d_base ≤ d_cover ≤ h · d_base    (for all h ≥ 1)

with no counterexamples reported.

What this module produces
=========================

Given an input BB code `(A, B, G = Z_ℓ × Z_m)`, this module:

1. Enumerates all **valid base codes**: triples `(A', B', G' = Z_{ℓ'} × Z_{m'})`
   where `ℓ' | ℓ`, `m' | m`, `(ℓ', m') ≠ (ℓ, m)`, and `A', B'` are the
   projections of `A, B` modulo `(ℓ', m')`. The validity check requires
   that the projected polynomials yield a CSS-commuting BB code (this
   is automatic for the projection direction, since `A B + B A = 0` in
   `F₂[Z_ℓ × Z_m]` passes through projection).

2. For each valid base, computes the cover index `h = (ℓ · m) / (ℓ' · m')`,
   classifies it as **rigorous** (h odd) or **conjectural** (h even).

3. Looks up the base's distance via a caller-supplied function
   `base_distance(A', B', G') → int | None`. The caller is expected
   to know the base distance from the corpus, the Bravyi table, or
   a SAT call.

4. Returns the maximum lower bound across all valid bases, separately
   for the rigorous-only and conjectural cases.

The module does **not** itself solve the base-distance lookup: that
side is the caller's responsibility, because base-code distances are
already in `bb_instances.duckdb` for the small instances and in
`instances/bravyi_table.yaml` for the reference instances.

Why this does NOT re-instate §6j
================================

The §6j obstruction (HANDOFF §6j) was: every character-theoretic
distance bound for abelian codes requires `gcd(|G|, q) = 1`, and
gross has `|G| = 72 = 2³ · 9` so F₂[G] is non-semisimple, blocking
the entire family.

SRB 2025's chain-map argument does **not** decompose F₂[G] via
characters at any step. It works on the bare F₂-vector-space chain
complex `Q• : F₂^{lm} → F₂^{2lm} → F₂^{lm}` with boundary maps given
by `H_X = (A | B)` and `H_Z^T = (B / A)^T`. Group elements appear only
as basis indices, never as characters. So §6j does not directly apply.

A new family-specific obstruction does apply: SRB Theorem 4.6 / 4.7
both need **h odd**, which for gross (the natural h=2 cover of
[[72,12,6]]) fails — see notes/T2R5.0_literature.md and the proposed
§6k obstruction.

How this module fits the lab's pattern
======================================

Same shape as `bb_ht_bound` and `bb_ht_condition` in `ht_roos.py`:

  • `bb_homological_bound(A, B, G, base_distance_fn) → int`:
    lower bound on `d_X = d_Z = d` from the SRB chain-map argument.
    Returns the max bound across valid bases. **By default uses the
    conjectural form** (any h ≥ 1) to give the strongest answer; pass
    `require_rigorous=True` to restrict to h odd.

  • `bb_homological_condition(A, B, G) → tuple[bool, str]`:
    whether at least one valid base code exists. If `require_rigorous`
    is True (default), also requires that the corresponding h is odd.

  • `enumerate_base_codes(A, B, G) → list[BaseCover]`:
    raw enumeration; the workhorse used by the bound and condition
    functions. Returns a list of BaseCover records.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Iterable

from .group import AbelianGroup, ZmZn
from .poly import Poly


# ---------------------------------------------------------------------------
# Data types
# ---------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class BaseCover:
    """A valid base code identified for a given cover code.

    Convention matches Symons-Rajput-Browne 2025 Theorem 3.1:
    cover `(Ã, B̃, l̃, m̃)`, base `(A', B', l', m')`,
    with `l̃ = u · l'`, `m̃ = t · m'`, `h = u · t = (l̃ m̃) / (l' m')`.

    `A'` is the projection of the cover's `Ã` via
        Mod(α̃_i, ℓ') for each monomial exponent of Ã (and similarly for m').

    `is_rigorous` flags whether SRB Theorem 4.7 applies directly
    (h odd), as opposed to the SRB §7 conjecture (any h).
    """

    A_base: Poly
    B_base: Poly
    G_base: AbelianGroup  # Z_{l'} × Z_{m'}
    u: int                # ℓ̃ / ℓ'
    t: int                # m̃ / m'
    h: int                # u · t — cover index

    @property
    def is_rigorous(self) -> bool:
        """True iff the chain-map theorem applies (h odd, see SRB Lemma 4.4)."""
        return self.h % 2 == 1


# ---------------------------------------------------------------------------
# Base-code enumeration
# ---------------------------------------------------------------------------


def _divisors(n: int) -> list[int]:
    """Positive divisors of n in increasing order. n ≥ 1."""
    if n < 1:
        raise ValueError(f"n must be ≥ 1, got {n}")
    out: list[int] = []
    i = 1
    while i * i <= n:
        if n % i == 0:
            out.append(i)
            if i != n // i:
                out.append(n // i)
        i += 1
    return sorted(out)


def _project_poly_mod(
    poly: Poly,
    G_cover: AbelianGroup,
    G_base: AbelianGroup,
) -> Poly:
    """Project a polynomial over `Z_ℓ̃ × Z_m̃` down to `Z_ℓ' × Z_m'`.

    The projection sends each monomial exponent vector `(a, b)` to
    `(a mod ℓ', b mod m')`. Two cover monomials that collide on this
    map cancel in F₂.

    Implements SRB Theorem 4.1 / Remark 6: `p(x^ã y^b̃) := x^{Mod(ã,ℓ')}
    y^{Mod(b̃,m')}`, extended linearly over F₂.

    Per the BB-code convention of this module, only abelian groups of
    rank ≤ 2 are supported (matching the BB-paper's `G = Z_ℓ × Z_m`).
    """
    if G_cover.rank != G_base.rank:
        raise ValueError("cover and base groups must have same rank")
    if poly.group != G_cover:
        raise ValueError("poly's group does not match the cover group")
    # Per-axis projection.
    factors_cover = G_cover.orders
    factors_base = G_base.orders
    if any(c % b != 0 for c, b in zip(factors_cover, factors_base)):
        raise ValueError(
            f"each base order must divide the corresponding cover order; "
            f"got base={factors_base}, cover={factors_cover}"
        )
    new_support: dict[tuple[int, ...], int] = {}
    for g in poly.support:
        projected = tuple(gi % b for gi, b in zip(g, factors_base))
        new_support[projected] = new_support.get(projected, 0) + 1
    final = frozenset(g for g, c in new_support.items() if c % 2 == 1)
    return Poly(support=final, group=G_base)


def enumerate_base_codes(
    A: Poly,
    B: Poly,
    G: AbelianGroup | None = None,
) -> list[BaseCover]:
    """Enumerate all candidate base codes `(A', B', G')` whose projection
    yields the given cover `(A, B, G)`.

    Strategy: enumerate divisors of each cyclic factor of G; for each
    proper sub-product `(ℓ', m', ...) | (ℓ, m, ...)`, define
    `G' = Z_{ℓ'} × Z_{m'} × ...` and project `A, B` down via
    `_project_poly_mod`. Each proper divisor pair yields one BaseCover.

    The covering index is `h = |G| / |G'|`.

    By "proper", we mean `(ℓ', m', ...) ≠ (ℓ, m, ...)`, i.e. excluding
    the trivial 1-cover.

    Constraints in this implementation
    ----------------------------------

    * Only abelian groups of rank ≤ 2 are accepted (the BB-code
      convention). Higher-rank generalizations are possible but not
      tested for this round.
    * The projection always preserves CSS commutation
      (`A * B + B * A = 0` over F₂[G] passes through projection),
      so no commutation re-check is needed.
    * The resulting base BB code may be degenerate (e.g. `B' = 0`),
      in which case its distance is ill-defined / 1. The
      `bb_homological_bound` consumer will just ignore base codes
      with `base_distance ≤ 1`.

    Returns
    -------
    A list of `BaseCover` records, one per proper divisor pair. May
    be empty if `G` has only the trivial 1-cover divisor pair
    (e.g. `|G| = 1`, which never happens for BB codes).
    """
    if G is None:
        G = A.group
    if A.group != B.group:
        raise ValueError("A and B must live in the same group algebra")
    if G != A.group:
        raise ValueError("G must equal A.group / B.group")
    if G.rank > 2:
        raise NotImplementedError(
            f"only rank ≤ 2 abelian groups supported in v0; got rank={G.rank}"
        )
    out: list[BaseCover] = []
    factors = G.orders
    if G.rank == 1:
        (ell,) = factors
        for ell_p in _divisors(ell):
            if ell_p == ell:
                continue  # trivial 1-cover excluded
            G_base = AbelianGroup((ell_p,))
            A_base = _project_poly_mod(A, G, G_base)
            B_base = _project_poly_mod(B, G, G_base)
            u = ell // ell_p
            out.append(
                BaseCover(
                    A_base=A_base,
                    B_base=B_base,
                    G_base=G_base,
                    u=u,
                    t=1,
                    h=u,
                )
            )
        return out
    # rank == 2
    ell, m = factors
    for ell_p in _divisors(ell):
        for m_p in _divisors(m):
            if (ell_p, m_p) == (ell, m):
                continue  # trivial 1-cover
            G_base = AbelianGroup((ell_p, m_p))
            A_base = _project_poly_mod(A, G, G_base)
            B_base = _project_poly_mod(B, G, G_base)
            u = ell // ell_p
            t = m // m_p
            out.append(
                BaseCover(
                    A_base=A_base,
                    B_base=B_base,
                    G_base=G_base,
                    u=u,
                    t=t,
                    h=u * t,
                )
            )
    return out


# ---------------------------------------------------------------------------
# The lower bound
# ---------------------------------------------------------------------------


def bb_homological_bound(
    A: Poly,
    B: Poly,
    G: AbelianGroup | None = None,
    *,
    base_distance: Callable[[Poly, Poly, AbelianGroup], int | None] | None = None,
    require_rigorous: bool = False,
) -> int:
    """Lower bound on the X- and Z-distance of the BB code `(A, B, G)`
    via the **Symons-Rajput-Browne 2025 cover-graph chain-map transfer**:

        d_cover ≥ d_base    (if (A, B, G) is an h-fold cover of (A', B', G'))

    Computation
    -----------

    1. Enumerate all candidate base codes via `enumerate_base_codes`.
    2. For each base, look up its distance via the caller-supplied
       `base_distance(A', B', G')` callable.
    3. Apply the SRB bound: candidate lower bound on `d_cover` is the
       base distance `d_base`.
    4. Return the **max** candidate lower bound across all bases.

    Parameters
    ----------
    A, B : Poly
        Defining polynomials of the cover BB code, in `F₂[G]`.
    G : AbelianGroup, optional
        The cover group `Z_ℓ × Z_m`. Defaults to `A.group`.
    base_distance : Callable[(A', B', G'), int | None], optional
        Returns the X-distance of the base code, or `None` if unknown.
        If `None` is returned (or no callable is provided), that base
        contributes nothing to the bound.
    require_rigorous : bool, default False
        If True, only count bases where `h = u·t` is odd (so SRB
        Theorem 4.7 strictly applies). If False, also count even-h
        bases under the SRB §7 conjecture.

    Returns
    -------
    int
        Lower bound on `d_cover`. Returns `1` (trivial) when no usable
        base is found — same convention as `bb_ht_bound`.

    Notes
    -----

    For the gross [[144,12,12]] code with `G = Z_12 × Z_6`:

    * Candidate base [[72,12,6]] (Z_6 × Z_6, h=2): in conjectural mode,
      contributes 6 to the lower bound. In rigorous mode, **discarded
      (h=2 even)**.
    * Other proper divisor pairs give degenerate or trivial-distance
      base codes that don't help.

    So `bb_homological_bound(grossA, grossB, Z_12 × Z_6)` returns
    6 (conjectural) or 1 (rigorous, since no odd-h base exists).
    Neither hits the target d=12. This is the structural-tightness
    limit articulated in notes/T2R5.0_literature.md §5 (proposed §6k
    obstruction).

    Compatibility with the program's "weight invariant" discipline
    ---------------------------------------------------------------

    The RHS quantity `d_base` is itself a code's minimum-weight
    invariant — it's a Hamming-weight infimum over a non-trivial
    homology class. So this bound stays on the right side of HANDOFF
    §6h ("dimension counts are not weight invariants"). No dimensional
    quantity (rank, kernel-dim, orbit-size) appears in the bound.
    """
    if G is None:
        G = A.group
    if A.group != B.group:
        raise ValueError("A and B must live in the same group algebra")

    if base_distance is None:
        # No way to compute; return trivial.
        return 1

    bases = enumerate_base_codes(A, B, G)
    best = 1
    for base in bases:
        if require_rigorous and not base.is_rigorous:
            continue
        d_base = base_distance(base.A_base, base.B_base, base.G_base)
        if d_base is None or d_base <= 1:
            continue
        if d_base > best:
            best = d_base
    return best


def bb_homological_condition(
    A: Poly,
    B: Poly,
    G: AbelianGroup | None = None,
    *,
    base_distance: Callable[[Poly, Poly, AbelianGroup], int | None] | None = None,
    require_rigorous: bool = False,
) -> tuple[bool, str]:
    """Structural condition for the bound to fire non-trivially.

    Returns (True, "ok") iff `bb_homological_bound` returns > 1 — i.e.
    there is at least one valid base code (a) with a known
    `base_distance > 1` and (b) satisfying the rigorous / conjectural
    mode constraint.

    Returns (False, reason) otherwise, with a short diagnostic.

    Diagnostics:

    * `"no_proper_cover"` — `|G| = 1` (impossible for BB) or only
      the trivial 1-cover divisor pair.
    * `"no_base_distance_callable"` — caller didn't pass one.
    * `"no_usable_base"` — at least one base exists but none has
      a usable known distance (`None` or `≤ 1`).
    * `"only_even_h_bases"` — in rigorous mode, all bases have h even.
    """
    if G is None:
        G = A.group
    if base_distance is None:
        return False, "no_base_distance_callable"
    bases = enumerate_base_codes(A, B, G)
    if not bases:
        return False, "no_proper_cover"
    any_rigorous = False
    any_usable_distance = False
    for base in bases:
        if base.is_rigorous:
            any_rigorous = True
        d_base = base_distance(base.A_base, base.B_base, base.G_base)
        if d_base is not None and d_base > 1:
            if require_rigorous and not base.is_rigorous:
                continue
            any_usable_distance = True
    if not any_usable_distance:
        if require_rigorous and not any_rigorous:
            return False, "only_even_h_bases"
        return False, "no_usable_base"
    return True, "ok"


# ---------------------------------------------------------------------------
# Upper bound (companion, also from SRB)
# ---------------------------------------------------------------------------


def bb_homological_upper_bound(
    A: Poly,
    B: Poly,
    G: AbelianGroup | None = None,
    *,
    base_distance: Callable[[Poly, Poly, AbelianGroup], int | None] | None = None,
    require_rigorous: bool = False,
) -> int:
    """Companion **upper** bound from SRB 2025 Theorem 4.6:

        d_cover  ≤  h · d_base

    For each candidate base `(A', B', G')` with cover index `h`,
    `h · d_base` is an upper bound on `d_cover`. Returns the **min**
    candidate upper bound (the strongest).

    Used as a sanity check — if the lower bound from the lookup table
    exceeds an applicable upper bound, the data is inconsistent (one
    of the two `d_exact` values must be wrong, or the bound is being
    applied outside its conditions of validity).

    Returns
    -------
    int
        Upper bound on `d_cover`. Returns a large sentinel
        (`2 * |G|`, twice the qubit count) when no usable base is
        found — semantically "no finite upper bound from this
        argument".
    """
    if G is None:
        G = A.group
    if base_distance is None:
        return 2 * G.cardinality  # sentinel: trivial upper bound
    bases = enumerate_base_codes(A, B, G)
    best = 2 * G.cardinality
    for base in bases:
        if require_rigorous and not base.is_rigorous:
            continue
        d_base = base_distance(base.A_base, base.B_base, base.G_base)
        if d_base is None or d_base <= 1:
            continue
        candidate = base.h * d_base
        if candidate < best:
            best = candidate
    return best


# ---------------------------------------------------------------------------
# Helper: build a `base_distance` callable from a corpus dict
# ---------------------------------------------------------------------------


def base_distance_from_table(
    table: Iterable[tuple[Poly, Poly, AbelianGroup, int]],
) -> Callable[[Poly, Poly, AbelianGroup], int | None]:
    """Build a `base_distance` callable from a finite table of
    `(A, B, G, d)` rows.

    Looks up by exact `(A, B, G)` equality on the `Poly` records. If
    no row matches, returns `None`.

    Convenient for the Bravyi table or a small hand-built lookup. For
    the full corpus, use `base_distance_from_corpus` (defined in the
    eval script, not here, to keep this module self-contained from
    duckdb).
    """
    lookup: dict[tuple[frozenset, frozenset, tuple[int, ...]], int] = {}
    for A, B, G, d in table:
        key = (A.support, B.support, G.orders)
        lookup[key] = d

    def _lookup(A: Poly, B: Poly, G: AbelianGroup) -> int | None:
        key = (A.support, B.support, G.orders)
        return lookup.get(key)

    return _lookup
