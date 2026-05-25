"""F₂-valued polynomials over an abelian group (i.e. elements of F₂[G]).

A polynomial is represented by its support: a frozenset of group elements.
F₂ coefficients are 0/1, so support determines the polynomial.

The string format matches `pipeline/attempts/*/state.yaml`:

    'x^3 + y + y^2'       # grossA
    'y^3 + x + x^2'       # grossB
    '1 + x^2 + x^7'       # from the [[90,8,10]] instance

Convention: variables are `x, y, z, ...` for the 1st, 2nd, 3rd, ... cyclic
factor. Exponents reduce mod the corresponding order. The constant monomial
is spelled `1` (the empty product). Implicit products (e.g. `xy^2`) are
**not** accepted in v0 — they raise `ValueError`. The Bravyi-table
instances do not use them, and accepting them silently risks
disagreement with the Lean side.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Iterable

from .group import AbelianGroup


_VAR_NAMES = "xyzwvu"  # extend if the lab ever needs rank > 6
_TERM_RE = re.compile(
    r"\A\s*(?P<var>[a-z])(?:\s*\^\s*(?P<exp>\d+))?\s*\Z",
    re.IGNORECASE,
)
_CONST_RE = re.compile(r"\A\s*1\s*\Z")


def _parse_term(term: str, group: AbelianGroup) -> tuple[int, ...]:
    """Parse a single monomial like 'x', 'x^3', '1' into a group element."""
    if _CONST_RE.match(term):
        return tuple(0 for _ in group.orders)
    m = _TERM_RE.match(term)
    if not m:
        raise ValueError(
            f"poly parser: cannot parse monomial {term!r}; v0 only supports "
            "single-variable powers like 'x', 'y^3', or the constant '1'. "
            "Products like 'xy' or 'x^2 y' are unsupported."
        )
    var = m.group("var").lower()
    if var not in _VAR_NAMES[: group.rank]:
        raise ValueError(
            f"poly parser: variable {var!r} out of range for group of rank "
            f"{group.rank} (allowed: {list(_VAR_NAMES[: group.rank])})"
        )
    axis = _VAR_NAMES.index(var)
    exp = int(m.group("exp") or "1")
    out = [0] * group.rank
    out[axis] = exp % group.orders[axis]
    return tuple(out)


@dataclass(frozen=True, slots=True)
class Poly:
    """An element of F₂[G] represented by its support set."""

    support: frozenset[tuple[int, ...]]
    group: AbelianGroup

    @classmethod
    def from_string(cls, s: str, group: AbelianGroup) -> "Poly":
        """Parse a polynomial like ``'x^3 + y + y^2'``.

        Empty terms ('+ +', leading/trailing '+') are tolerated and produce
        the zero polynomial.
        """
        terms = [t.strip() for t in s.split("+")]
        # Two monomials at the same group element cancel (we're over F₂);
        # accumulate as a symmetric multiset, then take the parity.
        counts: dict[tuple[int, ...], int] = {}
        for t in terms:
            if not t:
                continue
            g = _parse_term(t, group)
            counts[g] = counts.get(g, 0) + 1
        support = frozenset(g for g, c in counts.items() if c % 2 == 1)
        return cls(support=support, group=group)

    @classmethod
    def from_support(
        cls, support: Iterable[tuple[int, ...]], group: AbelianGroup
    ) -> "Poly":
        return cls(
            support=frozenset(group.reduce(g) for g in support),
            group=group,
        )

    @classmethod
    def zero(cls, group: AbelianGroup) -> "Poly":
        return cls(support=frozenset(), group=group)

    def weight(self) -> int:
        return len(self.support)

    def coef(self, g: tuple[int, ...]) -> int:
        return 1 if self.group.reduce(g) in self.support else 0

    def __call__(self, g: tuple[int, ...]) -> int:
        return self.coef(g)

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Poly):
            return NotImplemented
        return self.group == other.group and self.support == other.support

    def __hash__(self) -> int:
        return hash((self.group, self.support))

    def canonical_string(self) -> str:
        """Deterministic string form, ordered by axis then exponent.

        Two polys with the same support always produce the same string.
        Used as the canonical key for the corpus.
        """
        if not self.support:
            return "0"
        terms: list[str] = []
        for g in sorted(self.support):
            terms.append(_monomial_to_string(g))
        return " + ".join(terms)


def _monomial_to_string(g: tuple[int, ...]) -> str:
    parts: list[str] = []
    for axis, exp in enumerate(g):
        if exp == 0:
            continue
        var = _VAR_NAMES[axis]
        parts.append(var if exp == 1 else f"{var}^{exp}")
    if not parts:
        return "1"
    return "*".join(parts) if len(parts) > 1 else parts[0]
