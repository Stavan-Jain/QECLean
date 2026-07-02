"""A10 descent-cover harness tests (plan §S1, the five test classes).

Contract:
  1. cocycle-model literal lifts == a9 product-model matrices (exactly,
     under the group isomorphism φ) for the axis classes; the split
     class matches AbelianGroup((2, ell, m)); cocycle group laws hold
     on random triples (the mixed class has no product cross-check, so
     its correctness rides on these laws + the uniform construction);
  2. control distances: Z3Z6 doc-verified pair x-literal d=8 (k=4),
     toric L=3 axis-literal d=3, gross-base x-literal d=12 (slow);
  3. fiberSum descent for random twists, all classes;
  4. d_X = d_Z on random twisted covers (the inversion duality);
  5. Lemma-L1 consequence: the (k, d) verdict multiset over the full
     descent space is Aut(H)-presentation-invariant (small base).
"""

from __future__ import annotations

import importlib.util
import itertools
import random
import sys
from pathlib import Path

import numpy as np
import pytest

LAB = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LAB / "src"))
sys.path.insert(0, str(LAB / "scripts"))


def _load(name: str):
    spec = importlib.util.spec_from_file_location(
        name, LAB / "scripts" / f"{name}.py"
    )
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


a10 = _load("a10_descent_covers")
a9 = _load("a9_lean_target_screen")
a5c = _load("a5_cover_cascade")

from bb_lab.checks import assert_css_commutation, bb_check_matrices
from bb_lab.group import AbelianGroup
from bb_lab.poly import Poly
from bb_lab.sat_distance import x_distance


rng = random.Random(1729)


# ---------------------------------------------------------------------------
# 1. group laws + product-model equality
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("cls", a10.CLASSES)
@pytest.mark.parametrize("ell,m", [(3, 3), (3, 6), (6, 6), (2, 4)])
def test_cover_group_laws(ell, m, cls):
    G = a10.CoverGroup(ell, m, *cls)
    elems = list(G)
    assert len(elems) == 2 * ell * m == G.cardinality
    assert len(set(map(G.index, elems))) == G.cardinality
    zero = (0, 0, 0)
    for _ in range(200):
        g, h, k = (rng.choice(elems) for _ in range(3))
        assert G.add(g, G.add(h, k)) == G.add(G.add(g, h), k)
        assert G.add(g, h) == G.add(h, g)
        assert G.add(g, G.neg(g)) == zero
        assert G.add(g, zero) == g
        # proj is a homomorphism onto the base
        pa = ((g[1] + h[1]) % ell, (g[2] + h[2]) % m)
        assert G.proj(G.add(g, h)) == pa
    # deck: order-2, nonzero, spans ker(proj) fibers
    assert G.add(G.deck, G.deck) == zero and G.deck != zero
    for g in elems:
        fiber = [h for h in elems if G.proj(h) == G.proj(g)]
        assert sorted(fiber) == sorted([g, G.add(g, G.deck)])
        assert G.proj(G.sec(G.proj(g))) == G.proj(g)


@pytest.mark.parametrize("cls", [(1, 0), (0, 1), (0, 0)])
@pytest.mark.parametrize("ell,m", [(3, 3), (3, 6), (6, 6)])
def test_product_model_iso(ell, m, cls):
    G = a10.CoverGroup(ell, m, *cls)
    Gp, phi = a10.product_model(G)
    elems = list(G)
    # φ is a bijective homomorphism
    assert len({phi(g) for g in elems}) == G.cardinality == Gp.cardinality
    for _ in range(200):
        g, h = rng.choice(elems), rng.choice(elems)
        assert phi(G.add(g, h)) == Gp.add(phi(g), phi(h))


def _perm_from_phi(G, Gp, phi) -> np.ndarray:
    """pi[i] = Gp.index(phi(G.from_index(i)))."""
    return np.array([Gp.index(phi(g)) for g in G], dtype=np.int64)


@pytest.mark.parametrize("axis,cls", [("x", (1, 0)), ("y", (0, 1))])
def test_literal_lift_matches_a9(axis, cls):
    """Zero-twist axis covers == a9 cover_group/lift_poly matrices,
    exactly, after the φ reindexing (rows = checks, columns = qubits
    within each block)."""
    H = AbelianGroup((6, 6))
    A = Poly.from_string("y^3 + x + x^2", H)
    B = Poly.from_string("y^5 + x*y + x^2", H)  # hit5
    checks_c, Gc = a10.descent_checks(A, B, cls, (0, 0, 0), (0, 0, 0))
    Gp_expected = a9.cover_group(6, 6, axis)
    Gp, phi = a10.product_model(Gc)
    assert Gp.orders == Gp_expected.orders
    checks_p = bb_check_matrices(a9.lift_poly(A, Gp), a9.lift_poly(B, Gp))
    n = Gc.cardinality
    pi = _perm_from_phi(Gc, Gp, phi)
    for M_c, M_p in ((checks_c.H_X, checks_p.H_X), (checks_c.H_Z, checks_p.H_Z)):
        # rows: group elements; columns: [A-block | B-block]
        left = M_p[np.ix_(pi, pi)]
        right = M_p[np.ix_(pi, n + pi)]
        assert np.array_equal(M_c[:, :n], left)
        assert np.array_equal(M_c[:, n:], right)


def test_split_zero_twist_is_double_copy():
    """Split class, zero twist = two disjoint base copies: k doubles,
    d stays d_base."""
    H = AbelianGroup((3, 3))
    A = Poly.from_string("1 + x", H)
    B = Poly.from_string("1 + y", H)  # toric L=3: [[18,2,3]]
    checks, _ = a10.descent_checks(A, B, (0, 0), (0, 0), (0, 0))
    assert a10.code_k(checks) == 4
    d, _ = a10.exact_distance(checks, cap=6)
    assert d == 3


# ---------------------------------------------------------------------------
# 2. control distances
# ---------------------------------------------------------------------------


def test_control_z3z6_pair72():
    """The PR#53 Lean-proven pair: [[36,4,4]] x-cover → [[72,4,8]]."""
    H = AbelianGroup((3, 6))
    A = Poly.from_string("x^2 + y + y^3", H)
    B = Poly.from_string("1 + x + y^2", H)
    checks, _ = a10.descent_checks(A, B, (1, 0), (0, 0, 0), (0, 0, 0))
    assert a10.code_k(checks) == 4
    assert checks.num_qubits == 72
    d, _ = a10.exact_distance(checks, cap=9)
    assert d == 8


def test_control_toric3_axis_literal():
    """Toric L=3 x-literal cover: distance stays L = 3 (min-axis)."""
    H = AbelianGroup((3, 3))
    A = Poly.from_string("1 + x", H)
    B = Poly.from_string("1 + y", H)
    checks, _ = a10.descent_checks(A, B, (1, 0), (0, 0), (0, 0))
    assert a10.code_k(checks) == 2
    d, _ = a10.exact_distance(checks, cap=7)
    assert d == 3


@pytest.mark.slow
def test_control_gross_base_x_literal_is_gross():
    """Gross-base x-literal cover IS gross: d = 12 (the expensive
    control; UNSAT through 11 at n = 144)."""
    H = AbelianGroup((6, 6))
    A = Poly.from_string("x^3 + y + y^2", H)
    B = Poly.from_string("y^3 + x + x^2", H)
    checks, _ = a10.descent_checks(A, B, (1, 0), (0, 0, 0), (0, 0, 0))
    assert a10.code_k(checks) == 12
    assert checks.num_qubits == 144
    d, _ = a10.exact_distance(checks, cap=12)
    assert d == 12


# ---------------------------------------------------------------------------
# 3. fiberSum descent
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("cls", a10.CLASSES)
def test_fiber_sum_descent(cls):
    H = AbelianGroup((6, 6))
    A = Poly.from_string("y^3 + x + x^2", H)
    B = Poly.from_string("1 + x*y^5 + x^2*y", H)  # hit2
    Gc = a10.CoverGroup(6, 6, *cls)
    for _ in range(20):
        epsA = tuple(rng.randint(0, 1) for _ in range(3))
        epsB = tuple(rng.randint(0, 1) for _ in range(3))
        Ac = a10.twisted_lift(A, Gc, epsA)
        Bc = a10.twisted_lift(B, Gc, epsB)
        assert len(Ac.support) == 3 and len(Bc.support) == 3
        assert a10.fiber_sum(Ac, H) == A
        assert a10.fiber_sum(Bc, H) == B


@pytest.mark.parametrize("cls", a10.CLASSES)
def test_css_commutation_twisted(cls):
    H = AbelianGroup((6, 6))
    A = Poly.from_string("y^3 + x + x^2", H)
    B = Poly.from_string("y^5 + x*y + x^2", H)
    for _ in range(5):
        epsA = tuple(rng.randint(0, 1) for _ in range(3))
        epsB = tuple(rng.randint(0, 1) for _ in range(3))
        checks, _ = a10.descent_checks(A, B, cls, epsA, epsB)
        assert_css_commutation(checks)


# ---------------------------------------------------------------------------
# 4. inversion duality d_X = d_Z on twisted covers
# ---------------------------------------------------------------------------


def _swapped(checks):
    from bb_lab.checks import CheckMatrices

    return CheckMatrices(group=checks.group, H_X=checks.H_Z, H_Z=checks.H_X)


@pytest.mark.parametrize("cls", a10.CLASSES)
def test_duality_spot_check(cls):
    H = AbelianGroup((3, 3))
    A = Poly.from_string("1 + x", H)
    B = Poly.from_string("1 + y", H)
    for _ in range(4):
        epsA = tuple(rng.randint(0, 1) for _ in range(2))
        epsB = tuple(rng.randint(0, 1) for _ in range(2))
        checks, _ = a10.descent_checks(A, B, cls, epsA, epsB)
        if a10.code_k(checks) == 0:
            continue
        dX, _ = a10.exact_distance(checks, cap=12)
        dZ, _ = a10.exact_distance(_swapped(checks), cap=12)
        assert dX == dZ


# ---------------------------------------------------------------------------
# 5. Lemma-L1 consequence: presentation invariance of the verdict profile
# ---------------------------------------------------------------------------


def _verdict_profile(A: Poly, B: Poly, cap: int) -> tuple:
    prof = []
    for cls, epsA, epsB in a10.enumerate_covers(
        len(A.support), len(B.support)
    ):
        checks, _ = a10.descent_checks(A, B, cls, epsA, epsB)
        k = a10.code_k(checks)
        if k == 0:
            prof.append((0, None))
            continue
        d, _ = a10.exact_distance(checks, cap=cap)
        prof.append((k, d))  # d = None means d > cap
    return tuple(sorted(prof, key=lambda t: (t[0], t[1] or 10**9)))


def test_l1_presentation_invariance():
    """Full-descent-space (k, d) multisets agree across Aut(H)-moved
    presentations of the same base code (toric L=3; d capped at 7)."""
    H = AbelianGroup((3, 3))
    A = Poly.from_string("1 + x", H)
    B = Poly.from_string("1 + y", H)
    base_prof = _verdict_profile(A, B, cap=7)
    autos = a5c.automorphisms(3, 3)
    for auto in rng.sample(list(autos), 2):
        A2 = a5c.apply_auto(A, auto, H)
        B2 = a5c.apply_auto(B, auto, H)
        assert _verdict_profile(A2, B2, cap=7) == base_prof
