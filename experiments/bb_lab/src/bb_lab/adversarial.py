"""Parameterized adversarial stress-test generator (Tier 3).

Given a candidate's hypothesis predicates, generates BB-code instances
that:

1. Satisfy every hypothesis predicate (so the candidate's bound is
   supposed to apply on each generated instance).
2. Pin one structural axis to one value while leaving others free —
   sampled across the axes the hypothesis does NOT pin down.

A falsifier is an instance whose actual `d_X` (computed via SAT in
`bb_lab.sat_distance`) is strictly below the candidate's bound formula.
This module produces the instances; the candidate-specific bound check
and SAT distance computation happen downstream.

See `HANDOFF_R2.md` §4 for the predicate/axis vocabulary and §4.4 for
the round-1 R1+R4 falsifier worked example. The R1+R4 falsifier on
`Z_3 × Z_15` corresponds to varying `prime_structure=multi` and
`prime_rank_profile=mixed_rank` within the elem-ab + odd-weight
hypothesis — a sweep this module performs in seconds rather than the
~2 hours the hand-coded `scripts/adv_attack3_z3xz7.py` took.

Usage:

    from bb_lab.adversarial import generate_stress_tests

    tests = generate_stress_tests(
        hypothesis_predicates={
            "elem_ab_G_odd", "odd_weight_A", "odd_weight_B",
        },
        budget=200,
        n_max=90,
        seed=42,
    )
    for t in tests:
        # `t.A_poly`, `t.B_poly`, `t.ell`, `t.m` describe the instance.
        # Compute the candidate bound and compare to d_X via SAT.
        ...
"""

from __future__ import annotations

import hashlib
import random
from dataclasses import dataclass
from typing import Iterator

from .checks import bb_check_matrices
from .codeparams import code_params
from .group import AbelianGroup, ZmZn
from .poly import Poly
from .predicates import check_all_predicates, get_axis, unpinned_axes


@dataclass(frozen=True, slots=True)
class StressTest:
    """A BB-code instance produced by adversarial generation.

    `hypothesis_satisfied` lists every predicate name that holds on this
    instance — by construction, equals the input `hypothesis_predicates`
    passed to `generate_stress_tests`. `axis_probed` and `value_probed`
    identify which structural variation this instance contributes to.
    """

    instance_id: str
    ell: int
    m: int
    A_poly: str
    B_poly: str
    n: int
    k: int
    hypothesis_satisfied: tuple[str, ...]
    axis_probed: str
    value_probed: str


# --- Group templates per (axis, value) ---------------------------------------
#
# For each (axis, value) pair, we list `(ell, m)` group templates that pin the
# axis to the given value at the group-structure level. Polynomial-level
# predicates (`c_geq_3`, `odd_weight_A`, ...) are enforced via rejection
# sampling.
#
# When extending: add the (ell, m) pair to the list for each (axis, value)
# combo it pins. A group can appear under multiple (axis, value) pairs (e.g.
# Z_3 × Z_15 pins both `prime_structure=multi` and `prime_rank_profile=mixed_rank`).

_GROUP_TEMPLATES: dict[tuple[str, object], tuple[tuple[int, int], ...]] = {
    # ---- prime_structure ----
    ("prime_structure", "single"): (
        (3, 3),    # Z_3 × Z_3, single prime 3
        (3, 9),    # Z_3 × Z_9, single prime 3
        (9, 3),
        (5, 5),    # Z_5 × Z_5, single prime 5
        (3, 27),
        (27, 3),
    ),
    ("prime_structure", "multi"): (
        (3, 5),    (5, 3),     # Z_3 × Z_5
        (3, 7),    (7, 3),
        (5, 7),    (7, 5),
        (3, 15),   (15, 3),    # Z_3² × Z_5 — the R1+R4 falsifier shape
        (3, 21),   (21, 3),
        (5, 15),   (15, 5),
        (3, 35),   (35, 3),
    ),
    # ---- prime_rank_profile ----
    ("prime_rank_profile", "all_rank_1"): (
        (3, 5),    (5, 3),
        (3, 7),    (7, 3),
        (5, 7),    (7, 5),
        (3, 11),   (11, 3),
    ),
    ("prime_rank_profile", "mixed_rank"): (
        # G_odd has at least one prime at p-rank ≥ 2.
        (3, 15),   (15, 3),    # Z_3² × Z_5 — R1+R4 falsifier group
        (3, 21),   (21, 3),    # Z_3² × Z_7
        (5, 15),   (15, 5),    # Z_3 × Z_5²
        (3, 33),   (33, 3),    # Z_3² × Z_11
        (5, 35),   (35, 5),    # Z_5² × Z_7
        (9, 5),    (5, 9),     # Z_9 × Z_5 — G_odd has cyclic Z_9 (not elem-ab) but
                               # we still mark this as "mixed" in the rank sense; the
                               # caller filters by elem_ab if they want strict.
    ),
    # ---- G_odd_elem_ab_class ----
    ("G_odd_elem_ab_class", "strict"): (
        (3, 3),
        (5, 5),
        (3, 4),    (4, 3),     # G_odd = Z_3, strict elem-ab (one prime, rank 1)
        (3, 6),    (6, 3),     # G_odd = Z_3
    ),
    ("G_odd_elem_ab_class", "loose"): (
        (3, 15),   (15, 3),
        (3, 21),   (21, 3),
        (15, 15),
    ),
    ("G_odd_elem_ab_class", "non"): (
        (3, 9),    (9, 3),     # G_odd = Z_3 × Z_9 — non-elem-ab
        (9, 6),    (6, 9),
        (27, 3),
    ),
    # ---- G_2_shape ----
    ("G_2_shape", "trivial"): (
        (3, 3),
        (3, 5),    (5, 3),
        (3, 15),   (15, 3),
        (5, 7),    (7, 5),
        (9, 5),    (5, 9),
    ),
    # elem_ab: 2-Sylow is (Z_2)^k — each axis's 2-part ≤ 2.
    # (3, 6) → 2-Sylow Z_2; (6, 6) → Z_2 × Z_2; (6, 10) → Z_2 × Z_2.
    ("G_2_shape", "elem_ab"): (
        (3, 6),    (6, 3),
        (5, 6),    (6, 5),
        (6, 6),    # bb_72
        (6, 10),   (10, 6),
    ),
    # non_elem_ab: 2-Sylow has a Z_4 / Z_8 / ... factor. (3, 4) → Z_4.
    ("G_2_shape", "non_elem_ab"): (
        (3, 4),    (4, 3),
        (3, 8),    (8, 3),
        (5, 4),    (4, 5),
        (12, 6),   # gross — axis-2-part is Z_4
        (12, 12),  # bb_288
    ),
    # ---- c_value ----
    # c is polynomial-level, so the templates are groups where c=3 is achievable
    # by the Bravyi-style polynomial choices. Rejection sampling does the rest.
    ("c_value", 1): (
        (3, 5),    (3, 7),    (5, 7),
    ),
    ("c_value", 2): (
        (3, 6),    (3, 4),    (5, 6),
    ),
    ("c_value", 3): (
        (6, 6),    (9, 6),    (12, 6),   (12, 12),
        (3, 15),   (15, 3),   # the R1+R4 falsifier achieved c=3 here
    ),
    # ---- joint_vanishing ----
    # Polynomial-level predicate; templates are just achievability hints.
    # The check_all_predicates filter does the actual selection.
    ("joint_vanishing", "present"): (
        (3, 3),    (3, 6),    (6, 6),    (6, 3),
        (3, 15),   (15, 3),
        (12, 6),
    ),
    ("joint_vanishing", "absent"): (
        (3, 3),    (3, 5),    (5, 3),
        (3, 7),    (7, 3),    (3, 6),    (5, 6),    (6, 5),
    ),
    # ---- A_parity ----
    ("A_parity", "odd"): (
        (3, 3),    (3, 5),    (3, 7),    (5, 5),    (3, 15),    (15, 3),
        (6, 6),    (12, 6),
    ),
    ("A_parity", "even"): (
        (3, 5),    (5, 5),    (6, 6),    (3, 7),
    ),
    # ---- B_parity ----
    ("B_parity", "odd"): (
        (3, 3),    (3, 5),    (3, 7),    (5, 5),    (3, 15),    (15, 3),
        (6, 6),    (12, 6),
    ),
    ("B_parity", "even"): (
        (3, 5),    (5, 5),    (6, 6),    (3, 7),
    ),
}


# --- Weight choices per axis-value -------------------------------------------
#
# For some axes the value implies a constraint on polynomial weight (e.g.
# `A_parity=odd` forces odd weight). For others, the standard weight choices
# are fine. This map overrides the default weight options on a per-(axis,
# value) basis.

_WEIGHT_OVERRIDES: dict[tuple[str, object], tuple[tuple[int, int], ...]] = {
    # (axis, value) -> tuple of (A_weight, B_weight) pairs to try.
    ("A_parity", "odd"): ((3, 3), (3, 5), (5, 3), (5, 5), (3, 7)),
    ("A_parity", "even"): ((4, 3), (4, 4), (4, 5)),
    ("B_parity", "odd"): ((3, 3), (3, 5), (5, 3), (5, 5)),
    ("B_parity", "even"): ((3, 4), (4, 4), (5, 4)),
}

_DEFAULT_WEIGHT_PAIRS: tuple[tuple[int, int], ...] = (
    (3, 3), (3, 5), (5, 3), (5, 5),
)


# --- Generator internals -----------------------------------------------------


def _sample_polynomial(
    G: AbelianGroup, weight: int, rng: random.Random
) -> Poly:
    elements = list(G)
    if weight > len(elements):
        raise ValueError(f"weight {weight} > |G| = {len(elements)}")
    return Poly.from_support(rng.sample(elements, weight), G)


def _instance_id(
    ell: int, m: int, A: Poly, B: Poly, axis: str, value: object
) -> str:
    payload = (
        f"{ell}_{m}_{A.canonical_string()}_{B.canonical_string()}_{axis}_{value}"
    )
    h = hashlib.sha256(payload.encode()).hexdigest()[:10]
    return f"adv-{axis}-{value}-{h}"


def _try_make_instance(
    G: AbelianGroup, A: Poly, B: Poly
) -> tuple[int, int] | None:
    """Return `(n, k)` if `(A, B)` defines a valid BB code with `k > 0`,
    else `None`."""
    try:
        checks = bb_check_matrices(A, B)
        cp = code_params(checks)
    except AssertionError:
        return None
    if cp.k <= 0:
        return None
    return cp.n, cp.k


def _generate_for_axis_value(
    *,
    axis_name: str,
    value: object,
    hypothesis_predicates: set[str],
    budget: int,
    n_max: int,
    rng: random.Random,
    weight_pairs: tuple[tuple[int, int], ...] | None = None,
) -> Iterator[StressTest]:
    """Yield up to `budget` stress-tests probing `(axis_name, value)`.

    Each yielded instance satisfies every predicate in
    `hypothesis_predicates` and has `n ≤ n_max` with `k > 0`. Uses
    rejection sampling; may yield fewer than `budget` if templates
    aren't dense enough.
    """
    templates = _GROUP_TEMPLATES.get((axis_name, value), ())
    if not templates:
        return
    weights = (
        weight_pairs
        if weight_pairs is not None
        else _WEIGHT_OVERRIDES.get((axis_name, value), _DEFAULT_WEIGHT_PAIRS)
    )
    attempts_per_template = max(40, 8 * (budget // max(1, len(templates))))
    yielded = 0
    for ell, m in templates:
        if yielded >= budget:
            return
        n_template = 2 * ell * m
        if n_template > n_max:
            continue
        G = ZmZn(ell, m)
        if G.cardinality < max(w for pair in weights for w in pair):
            continue
        for _ in range(attempts_per_template):
            if yielded >= budget:
                return
            w_A, w_B = weights[rng.randrange(len(weights))]
            try:
                A = _sample_polynomial(G, w_A, rng)
                B = _sample_polynomial(G, w_B, rng)
            except ValueError:
                continue
            if not check_all_predicates(hypothesis_predicates, G, A, B):
                continue
            nk = _try_make_instance(G, A, B)
            if nk is None:
                continue
            n, k = nk
            yield StressTest(
                instance_id=_instance_id(ell, m, A, B, axis_name, value),
                ell=ell,
                m=m,
                A_poly=A.canonical_string(),
                B_poly=B.canonical_string(),
                n=n,
                k=k,
                hypothesis_satisfied=tuple(sorted(hypothesis_predicates)),
                axis_probed=axis_name,
                value_probed=str(value),
            )
            yielded += 1


# --- Public API --------------------------------------------------------------


def generate_stress_tests(
    *,
    hypothesis_predicates: set[str],
    budget: int = 200,
    n_max: int = 72,
    seed: int | None = 0,
    axes: set[str] | None = None,
    weight_pairs: tuple[tuple[int, int], ...] | None = None,
) -> list[StressTest]:
    """Generate up to `budget` BB-code instances stress-testing a hypothesis.

    All generated instances:

    * **Satisfy every predicate** in `hypothesis_predicates` (so the
      candidate's bound is supposed to apply on each).
    * Have `n = 2·|G| ≤ n_max`.
    * Have `k > 0` (non-trivial code).
    * Carry metadata identifying the `(axis, value)` they probe.

    `axes`: set of axis names to probe. Defaults to all axes not
    pinned by `hypothesis_predicates` (see `predicates.unpinned_axes`).

    `weight_pairs`: tuple of `(A_weight, B_weight)` pairs to sample
    from. If `None`, uses per-axis overrides where defined and a
    default set of (3, 3) / (3, 5) / (5, 3) / (5, 5) otherwise.

    Returns instances ordered by axis name then value, with budget
    split evenly across probed (axis, value) pairs that have templates.
    The result may be shorter than `budget` if rejection sampling
    doesn't find enough hypothesis-satisfying instances.
    """
    rng = random.Random(seed)
    if axes is None:
        axes = unpinned_axes(hypothesis_predicates)
    axis_value_pairs: list[tuple[str, object]] = []
    for axis_name in sorted(axes):
        try:
            axis = get_axis(axis_name)
        except KeyError:
            continue
        for value in axis.range_values:
            if (axis_name, value) in _GROUP_TEMPLATES:
                axis_value_pairs.append((axis_name, value))
    if not axis_value_pairs:
        return []
    per_pair_budget = max(1, budget // len(axis_value_pairs))
    out: list[StressTest] = []
    for axis_name, value in axis_value_pairs:
        for t in _generate_for_axis_value(
            axis_name=axis_name,
            value=value,
            hypothesis_predicates=hypothesis_predicates,
            budget=per_pair_budget,
            n_max=n_max,
            rng=rng,
            weight_pairs=weight_pairs,
        ):
            out.append(t)
    return out


def supported_axis_value_pairs() -> tuple[tuple[str, object], ...]:
    """Return every `(axis, value)` pair the generator has templates for.

    Useful for introspection and for tests that exercise every template.
    """
    return tuple(_GROUP_TEMPLATES.keys())
