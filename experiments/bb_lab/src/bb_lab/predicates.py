"""Canonical predicate vocabulary for round-2 candidate hypotheses.

See `HANDOFF_R2.md` §4.1 (the predicate vocabulary) and §4.2 (the
structural axes pinned by each predicate). Every predicate is a
machine-checkable property of a BB-code instance `(G, A, B)`; a
candidate's hypothesis is a conjunction of predicates.

This module is the single source of truth for predicate names. Both
the candidate registry (storing `hypothesis_predicates` as JSON) and
the adversarial generator (computing unpinned axes from the
hypothesis) refer to the names registered here. Adding a new
predicate is a coordinated edit: add the check function here, add a
test, and (if it pins a new axis) extend `AXES`.

The check functions delegate to existing `degeneracy.py` /
`radical_weight.py` helpers; this module is glue and registry, not new
mathematics.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

from .degeneracy import (
    _prime_factorization,
    g_odd_decomposition,
    is_g_odd_elementary_abelian,
    is_non_degenerate,
)
from .group import AbelianGroup
from .poly import Poly


PredicateFn = Callable[[AbelianGroup, Poly, Poly], bool]


# --- Helpers (small, kept private) ------------------------------------------


def _prime_of_prime_power(q: int) -> int:
    """Return the unique prime dividing `q`. Raises if `q` isn't a prime power."""
    factors = _prime_factorization(q)
    if len(factors) != 1:
        raise ValueError(f"{q} is not a prime power (factorization: {factors})")
    return factors[0][0]


def _primes_of_G_odd(G: AbelianGroup) -> set[int]:
    """Set of distinct primes appearing in `G_odd`'s prime-power decomposition."""
    return {_prime_of_prime_power(q) for q in g_odd_decomposition(G)}


def _prime_multiplicities(G: AbelianGroup) -> dict[int, int]:
    """Map prime `p` to how many prime-`p` cyclic factors appear in `G_odd`.

    Example: `G = Z_3 × Z_15 ≅ Z_3 × Z_3 × Z_5` → `{3: 2, 5: 1}`.
    """
    counts: dict[int, int] = {}
    for q in g_odd_decomposition(G):
        p = _prime_of_prime_power(q)
        counts[p] = counts.get(p, 0) + 1
    return counts


# --- Predicate registry ------------------------------------------------------

PREDICATES: dict[str, PredicateFn] = {}


def _register(name: str) -> Callable[[PredicateFn], PredicateFn]:
    def deco(fn: PredicateFn) -> PredicateFn:
        if name in PREDICATES:
            raise RuntimeError(f"predicate {name!r} double-registered")
        PREDICATES[name] = fn
        return fn

    return deco


# Group-structure predicates


@_register("elem_ab_G_odd")
def _p_elem_ab_G_odd(G: AbelianGroup, A: Poly, B: Poly) -> bool:
    return is_g_odd_elementary_abelian(G)


@_register("strict_elem_ab_G_odd")
def _p_strict_elem_ab_G_odd(G: AbelianGroup, A: Poly, B: Poly) -> bool:
    return is_g_odd_elementary_abelian(G) and len(_primes_of_G_odd(G)) == 1


@_register("single_prime_G_odd")
def _p_single_prime_G_odd(G: AbelianGroup, A: Poly, B: Poly) -> bool:
    return len(_primes_of_G_odd(G)) == 1


@_register("multi_prime_G_odd")
def _p_multi_prime_G_odd(G: AbelianGroup, A: Poly, B: Poly) -> bool:
    return len(_primes_of_G_odd(G)) >= 2


@_register("G_odd_all_rank_1")
def _p_G_odd_all_rank_1(G: AbelianGroup, A: Poly, B: Poly) -> bool:
    return all(count == 1 for count in _prime_multiplicities(G).values())


@_register("G_odd_mixed_rank")
def _p_G_odd_mixed_rank(G: AbelianGroup, A: Poly, B: Poly) -> bool:
    return any(count >= 2 for count in _prime_multiplicities(G).values())


@_register("G_2_trivial")
def _p_G_2_trivial(G: AbelianGroup, A: Poly, B: Poly) -> bool:
    return G.cardinality % 2 == 1


def _largest_2_power(n: int) -> int:
    """Largest power of 2 dividing `n` (1 if `n` is odd, 0 if `n` is 0)."""
    if n == 0:
        return 0
    p = 1
    while n % (p * 2) == 0:
        p *= 2
    return p


@_register("G_2_elem_ab")
def _p_G_2_elem_ab(G: AbelianGroup, A: Poly, B: Poly) -> bool:
    """The 2-Sylow of `G = ∏ Z_{n_i}` is `(Z_2)^k` iff each axis's 2-part
    is ≤ 2 (no Z_4, Z_8, ...) — equivalently, each `n_i` is twice an
    odd number or odd."""
    return all(_largest_2_power(n) <= 2 for n in G.orders)


@_register("non_semisimple_F2G")
def _p_non_semisimple_F2G(G: AbelianGroup, A: Poly, B: Poly) -> bool:
    return G.cardinality % 2 == 0


# Degeneracy predicates


@_register("non_degenerate")
def _p_non_degenerate(G: AbelianGroup, A: Poly, B: Poly) -> bool:
    return is_non_degenerate(A, B, G)


@_register("degenerate")
def _p_degenerate(G: AbelianGroup, A: Poly, B: Poly) -> bool:
    return not is_non_degenerate(A, B, G)


@_register("c_geq_2")
def _p_c_geq_2(G: AbelianGroup, A: Poly, B: Poly) -> bool:
    # Local import to avoid circularity: radical_weight imports group/poly.
    from .radical_weight import joint_support_subgroup_index

    return joint_support_subgroup_index(A, B, G) >= 2


@_register("c_geq_3")
def _p_c_geq_3(G: AbelianGroup, A: Poly, B: Poly) -> bool:
    from .radical_weight import joint_support_subgroup_index

    return joint_support_subgroup_index(A, B, G) >= 3


@_register("c_eq_3_exact")
def _p_c_eq_3_exact(G: AbelianGroup, A: Poly, B: Poly) -> bool:
    """`c == 3` exactly. All 5 Bravyi-table codes satisfy this; the
    Lin–Pryadko denominator-cliff lives at `c = 3`."""
    from .radical_weight import joint_support_subgroup_index

    return joint_support_subgroup_index(A, B, G) == 3


# Polynomial-structure predicates


@_register("odd_weight_A")
def _p_odd_weight_A(G: AbelianGroup, A: Poly, B: Poly) -> bool:
    return A.weight() % 2 == 1


@_register("odd_weight_B")
def _p_odd_weight_B(G: AbelianGroup, A: Poly, B: Poly) -> bool:
    return B.weight() % 2 == 1


@_register("joint_vanishing_nonempty")
def _p_joint_vanishing_nonempty(G: AbelianGroup, A: Poly, B: Poly) -> bool:
    """∃ Frobenius orbit `O` on `Ĝ_odd` where both `A` and `B` vanish.

    Equivalent to "the joint-vanishing direct sum
    `⊕_O R_O` is nonempty in the sense used by Cv2 / R1+R4" — the
    bound's RHS is vacuous (∞) when this predicate fails on a given
    instance, so candidates whose hypothesis includes this are
    implicitly restricting to its true-region.
    """
    from .algebraic_features import (
        g_odd_frobenius_orbits,
        jacobson_radical_depth,
    )

    for orbit in g_odd_frobenius_orbits(G):
        if (
            jacobson_radical_depth(A, orbit, G) > 0
            and jacobson_radical_depth(B, orbit, G) > 0
        ):
            return True
    return False


# --- Public API --------------------------------------------------------------


def check_predicate(name: str, G: AbelianGroup, A: Poly, B: Poly) -> bool:
    """Evaluate a single predicate by name.

    Raises:
        KeyError if `name` isn't a registered predicate.
    """
    try:
        fn = PREDICATES[name]
    except KeyError:
        raise KeyError(
            f"unknown predicate {name!r}; registered: {sorted(PREDICATES)}"
        ) from None
    return fn(G, A, B)


def check_all_predicates(
    names: set[str], G: AbelianGroup, A: Poly, B: Poly
) -> bool:
    """True iff every predicate in `names` holds on `(G, A, B)`."""
    return all(check_predicate(n, G, A, B) for n in names)


def list_predicates() -> tuple[str, ...]:
    """Return the registered predicate names in alphabetical order."""
    return tuple(sorted(PREDICATES))


# --- Structural axes ---------------------------------------------------------


@dataclass(frozen=True, slots=True)
class StructuralAxis:
    """One dimension of variation across BB-code instances.

    `pinned_by_predicates` is the set of predicate names that, when
    present in a hypothesis, fix the axis to a specific value (or a
    bounded sub-range). The adversarial generator walks values on
    axes NOT pinned by the hypothesis.
    """

    name: str
    range_values: tuple
    pinned_by_predicates: frozenset[str]


AXES: tuple[StructuralAxis, ...] = (
    StructuralAxis(
        name="prime_structure",
        range_values=("single", "multi"),
        pinned_by_predicates=frozenset({"single_prime_G_odd", "multi_prime_G_odd"}),
    ),
    StructuralAxis(
        name="prime_rank_profile",
        range_values=("all_rank_1", "mixed_rank"),
        pinned_by_predicates=frozenset({"G_odd_all_rank_1", "G_odd_mixed_rank"}),
    ),
    StructuralAxis(
        name="G_odd_elem_ab_class",
        range_values=("strict", "loose", "non"),
        pinned_by_predicates=frozenset(
            {"elem_ab_G_odd", "strict_elem_ab_G_odd"}
        ),
    ),
    StructuralAxis(
        name="G_2_shape",
        range_values=("trivial", "elem_ab", "non_elem_ab"),
        pinned_by_predicates=frozenset(
            {"G_2_trivial", "G_2_elem_ab", "non_semisimple_F2G"}
        ),
    ),
    StructuralAxis(
        name="c_value",
        range_values=(1, 2, 3),
        pinned_by_predicates=frozenset(
            {"non_degenerate", "degenerate", "c_geq_2", "c_geq_3", "c_eq_3_exact"}
        ),
    ),
    StructuralAxis(
        name="joint_vanishing",
        range_values=("present", "absent"),
        pinned_by_predicates=frozenset({"joint_vanishing_nonempty"}),
    ),
    StructuralAxis(
        name="A_parity",
        range_values=("odd", "even"),
        pinned_by_predicates=frozenset({"odd_weight_A"}),
    ),
    StructuralAxis(
        name="B_parity",
        range_values=("odd", "even"),
        pinned_by_predicates=frozenset({"odd_weight_B"}),
    ),
)


def pinned_axes(hypothesis_predicates: set[str]) -> set[str]:
    """Return axis names pinned by the given hypothesis."""
    return {
        axis.name
        for axis in AXES
        if axis.pinned_by_predicates & hypothesis_predicates
    }


def unpinned_axes(hypothesis_predicates: set[str]) -> set[str]:
    """Return axis names NOT pinned by the hypothesis.

    These are the dimensions Tier-3 adversarial generation will probe.
    """
    return {axis.name for axis in AXES} - pinned_axes(hypothesis_predicates)


def get_axis(name: str) -> StructuralAxis:
    """Look up an axis by name. Raises KeyError if not registered."""
    for axis in AXES:
        if axis.name == name:
            return axis
    raise KeyError(
        f"unknown axis {name!r}; registered: {[a.name for a in AXES]}"
    )


# --- Deferred predicates ----------------------------------------------------
#
# These appear in `HANDOFF_R2.md` §4.1 but are NOT yet registered. Each is
# deferred for a specific reason; add the implementation when a round-2
# candidate actually needs the predicate.
#
# `weight_eq_A(w)`, `weight_eq_B(w)`
#   Parameterized predicates. Would require a "predicate factory"
#   mechanism (e.g. `make_weight_eq_A(w) -> PredicateFn`) and an
#   extension to the registry to handle parameterized names. For
#   round-2 MVP, parity predicates (`odd_weight_A` / `odd_weight_B`)
#   plus the `weight_pairs` argument to `adversarial.generate_stress_tests`
#   cover the cases R1+R4 used. Add the factory when a candidate
#   constrains specific weights other than parity.
#
# `no_weight_le_2_syzygy_AB`
#   Tightening filter from `notes/T3R2.5_tightening_filter.md`.
#   Requires enumerating weight-≤2 syzygies `(α, β) ∈ F_2[G]²` with
#   `αA + βB = 0`. Implementable but ~80 LOC of new code; defer until
#   a candidate's hypothesis actually uses it.
#
# `cover_index_eq_h(h)`, `cover_index_coprime_to_char`
#   Cover-graph predicates for chain-map family candidates. The §6k
#   obstruction means most chain-map candidates are pre-shelved
#   anyway. Defer until a chain-map candidate makes it past Tier 0.
#   When implemented, will need a `bb_lab.cover_index` module that
#   computes the cover decomposition of a BB code (Symons–Rajput–
#   Browne 2025 §3 — base/cover quotient computation).
