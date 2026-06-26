"""Difference-set predicates for the two-sided (Theorem A) distance argument.

The gross [[72,12,6]] base-distance proof has two halves. The *engine* half
(one-sided / annihilator splits) is governed by the F4 layer frame and is
locked to the Z6^2 group frame. The *two-sided* half (the (1,1)/(1,3)/(2,2)
splits) is, by contrast, **frame-agnostic** combinatorics: it depends only on
the difference-set structure of A and B, not on any F4/CRT decomposition.

This module packages the three predicates that drive the two-sided argument,
plus the Frobenius-square gate that the predicates must rule out.

Predicates (for A, B in F2[G], identified with their supports)
--------------------------------------------------------------
- **D1**  ``is_sidon``               : the difference multiset of supp(P) is
  multiplicity-free (``ov <= 1``: any two translates of supp(P) meet in <= 1
  cell). Enables the inclusion-exclusion weight count ``|P.z| = w|z| - 2p + ...``.
- **D2**  ``difference_sets_disjoint`` : ``dA ∩ dB = empty``. Kills the (1,1)
  split (A+h = B+r would force dA = dB).
- **D3**  ``coordinate_separated``   : on every cyclic axis, the projected
  difference sets are disjoint. Drives the projection (pi_x / pi_y)
  contradictions in the (1,3) and (2,2) splits.

The Frobenius obstruction
-------------------------
``D1 & D2`` alone do **not** imply a two-sided cycle floor of ``2w``. The
counterexample is the characteristic-2 Frobenius square: in F2[G],
``(1 + x + y)^2 = 1 + x^2 + y^2`` (Freshman's dream), so for ``A = B^2`` the
pair ``(1, B)`` is a two-sided cycle of weight ``1 + w < 2w``, while A, B are
both Sidon (D1) with ``dA = 2*dB`` disjoint from ``dB`` (D2). On e.g. Z7^2 this
gives a genuine weight-4 *logical* in a [[98,12,4]] code. The Frobenius square
violates D3 (it has ``0 in x(dA) ∩ x(dB)``), which is exactly why D3 is not
dispensable. See ``scripts/twosided_floor_counterexample.py`` and
``docs/gross-distance-extensibility.md``.

Empirically (SAT-checked over 4144 general weight-3 codes on Z6^2 and Z7^2),
``D1 & D2 & D3 => two-sided cycle floor >= 2w`` holds with zero violations.
This is the corrected, frame-agnostic adaptation criterion (still a conjecture
for general w; proven for the gross instance via the spike-spread argument).
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass

from .group import AbelianGroup
from .poly import Poly


def difference_set(P: Poly) -> set[tuple[int, ...]]:
    """The set of nonzero differences ``g - h`` for ``g != h`` in supp(P)."""
    G = P.group
    S = list(P.support)
    return {G.sub(g, h) for g in S for h in S if g != h}


def overlap_bound(P: Poly) -> int:
    """Max multiplicity in the difference *multiset* of supp(P).

    Equals ``max_{h != h'} |(supp P + h) ∩ (supp P + h')|`` (the ``ov`` of the
    proof). ``overlap_bound(P) <= 1`` is the Sidon / D1 condition.
    """
    G = P.group
    S = list(P.support)
    c = Counter(G.sub(g, h) for g in S for h in S if g != h)
    return max(c.values()) if c else 0


def is_sidon(P: Poly) -> bool:
    """D1: supp(P) is a Sidon set (all pairwise differences distinct, ov <= 1)."""
    return overlap_bound(P) <= 1


def difference_sets_disjoint(A: Poly, B: Poly) -> bool:
    """D2: ``dA ∩ dB = empty``."""
    _same_group(A, B)
    return difference_set(A).isdisjoint(difference_set(B))


def coordinate_separated(A: Poly, B: Poly) -> bool:
    """D3: on every cyclic axis, the projected difference sets are disjoint.

    For each axis ``i``, ``{d[i] : d in dA} ∩ {d[i] : d in dB} = empty``. This is
    the strong (all-axes) form satisfied by the gross polynomials; it is the
    hypothesis that excludes the Frobenius square.
    """
    _same_group(A, B)
    dA, dB = difference_set(A), difference_set(B)
    rank = A.group.rank
    for axis in range(rank):
        if not {d[axis] for d in dA}.isdisjoint({d[axis] for d in dB}):
            return False
    return True


def frobenius_square(P: Poly) -> Poly:
    """``P^2`` in F2[G]. By the char-2 Frobenius identity ``(sum b)^2 = sum b^2``,
    the support is the parity-of-multiplicity of the doubled support
    ``{2*b : b in supp P}`` (doubling each coordinate, mod the cyclic orders)."""
    G = P.group
    c: Counter[tuple[int, ...]] = Counter()
    for b in P.support:
        c[G.reduce(tuple(2 * bi for bi in b))] += 1
    supp = frozenset(g for g, m in c.items() if m % 2 == 1)
    return Poly(support=supp, group=G)


def is_translate(P: Poly, Q: Poly) -> bool:
    """True iff supp(P) is a translate of supp(Q): ``supp P = supp Q + t``."""
    _same_group(P, Q)
    SP, SQ = P.support, list(Q.support)
    if len(SP) != len(SQ):
        return False
    if not SP:
        return True
    G = P.group
    p0 = next(iter(SP))
    for q in SQ:
        t = G.sub(p0, q)
        if frozenset(G.add(s, t) for s in SQ) == SP:
            return True
    return False


def is_frobenius_related(A: Poly, B: Poly) -> bool:
    """Gate for the Frobenius-square obstruction.

    True iff ``A`` is a translate of ``B^2`` or ``B`` is a translate of ``A^2``.
    When true, the code carries a two-sided cycle of weight ``1 + |supp|`` (the
    pair ``(monomial, B)`` since ``A = t B^2`` gives ``A.t' = B.B``-type), so the
    two-sided floor argument fails regardless of D1/D2. Such pairs MUST be
    excluded (D3 does this) before claiming a ``2w`` floor.
    """
    _same_group(A, B)
    return is_translate(A, frobenius_square(B)) or is_translate(B, frobenius_square(A))


@dataclass(frozen=True, slots=True)
class TwoSidedHypothesis:
    """Summary of the two-sided-floor predicates for a pair (A, B)."""

    d1_A_sidon: bool
    d1_B_sidon: bool
    d2_disjoint: bool
    d3_coord_separated: bool
    frobenius_related: bool

    @property
    def d1(self) -> bool:
        return self.d1_A_sidon and self.d1_B_sidon

    @property
    def floor_hypothesis(self) -> bool:
        """The corrected, SAT-validated sufficient condition D1 & D2 & D3.

        Implies (conjecturally for general w; proven for the gross instance)
        a two-sided cycle floor of ``2w``. Note ``frobenius_related`` is always
        False when this holds.
        """
        return self.d1 and self.d2_disjoint and self.d3_coord_separated


def two_sided_hypothesis(A: Poly, B: Poly) -> TwoSidedHypothesis:
    """Evaluate all two-sided-floor predicates for a pair (A, B)."""
    _same_group(A, B)
    return TwoSidedHypothesis(
        d1_A_sidon=is_sidon(A),
        d1_B_sidon=is_sidon(B),
        d2_disjoint=difference_sets_disjoint(A, B),
        d3_coord_separated=coordinate_separated(A, B),
        frobenius_related=is_frobenius_related(A, B),
    )


def _same_group(A: Poly, B: Poly) -> None:
    if A.group != B.group:
        raise ValueError("A and B must live in the same group algebra")
