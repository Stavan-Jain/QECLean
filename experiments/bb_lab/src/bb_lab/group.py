"""Finite abelian groups ZMod n_1 × ... × ZMod n_d.

The Lab pins to ZMod ℓ × ZMod m for v0 (Bravyi BB codes), but the
representation is dimension-generic so v1 can add ZMod n_1 × ZMod n_2 × ZMod n_3
without touching the group layer.

Convention matches the Lean side
([QEC/Stabilizer/Framework/Homological/BBChainComplex.lean]):
group elements are tuples of ints in `[0, n_i)`; the convolution uses
subtraction `g - h` (not `h - g`), per `conv A f g = sum_h A(h) * f(g - h)`.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterator


@dataclass(frozen=True, slots=True)
class AbelianGroup:
    """Direct product of cyclic groups, written multiplicatively below
    even though stored additively (the BB literature swaps between).

    `orders` is the tuple `(n_1, ..., n_d)`; the group is
    `ZMod n_1 × ... × ZMod n_d` with cardinality `prod orders`.
    """

    orders: tuple[int, ...]

    def __post_init__(self) -> None:
        if not self.orders:
            raise ValueError("AbelianGroup needs at least one cyclic factor")
        for n in self.orders:
            if n <= 0:
                raise ValueError(f"cyclic order must be positive, got {n}")

    @property
    def rank(self) -> int:
        return len(self.orders)

    @property
    def cardinality(self) -> int:
        c = 1
        for n in self.orders:
            c *= n
        return c

    def __len__(self) -> int:
        return self.cardinality

    def __iter__(self) -> Iterator[tuple[int, ...]]:
        return self._iter([])

    def _iter(self, prefix: list[int]) -> Iterator[tuple[int, ...]]:
        axis = len(prefix)
        if axis == self.rank:
            yield tuple(prefix)
            return
        n = self.orders[axis]
        for i in range(n):
            prefix.append(i)
            yield from self._iter(prefix)
            prefix.pop()

    def reduce(self, g: tuple[int, ...]) -> tuple[int, ...]:
        if len(g) != self.rank:
            raise ValueError(f"element rank {len(g)} != group rank {self.rank}")
        return tuple(int(gi) % n for gi, n in zip(g, self.orders))

    def neg(self, g: tuple[int, ...]) -> tuple[int, ...]:
        return tuple((-gi) % n for gi, n in zip(g, self.orders))

    def add(self, g: tuple[int, ...], h: tuple[int, ...]) -> tuple[int, ...]:
        return tuple((gi + hi) % n for gi, hi, n in zip(g, h, self.orders))

    def sub(self, g: tuple[int, ...], h: tuple[int, ...]) -> tuple[int, ...]:
        return tuple((gi - hi) % n for gi, hi, n in zip(g, h, self.orders))

    def index(self, g: tuple[int, ...]) -> int:
        """Bijective row-major enumeration `g -> [0, |G|)`.

        Used for the column ordering of the check matrix; the Lean side
        does not pin a specific enumeration, so we are free to choose.
        Row-major matches numpy reshape conventions.
        """
        idx = 0
        for gi, n in zip(g, self.orders):
            idx = idx * n + (gi % n)
        return idx

    def from_index(self, i: int) -> tuple[int, ...]:
        if not 0 <= i < self.cardinality:
            raise IndexError(f"index {i} outside [0, {self.cardinality})")
        out: list[int] = []
        for n in reversed(self.orders):
            out.append(i % n)
            i //= n
        return tuple(reversed(out))

    def label(self) -> str:
        """Compact label for storage keys: 'Z12xZ6', 'Z9xZ9xZ3', ..."""
        return "x".join(f"Z{n}" for n in self.orders)


def ZmZn(ell: int, m: int) -> AbelianGroup:
    """Convenience constructor for the BB-paper convention `ZMod ℓ × ZMod m`."""
    return AbelianGroup((ell, m))
