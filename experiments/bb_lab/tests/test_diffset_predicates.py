"""Tests for `bb_lab.diffset_predicates`.

Anchors:
- gross base (Z6^2, A=x^3+y+y^2, B=y^3+x+x^2): satisfies D1, D2, D3; NOT
  Frobenius-related; floor_hypothesis holds.
- Frobenius square (Z6^2, A=1+x^2+y^2 = (1+x+y)^2, B=1+x+y): satisfies D1, D2
  but FAILS D3; IS Frobenius-related; floor_hypothesis fails. This is the
  counterexample to "D1 & D2 => 2w floor".
- [[36,4,4]] base (Z3xZ6, A=x^2+y+y^3, B=1+x+y^2): FAILS D2.
"""

from __future__ import annotations

from bb_lab.diffset_predicates import (
    coordinate_separated,
    difference_sets_disjoint,
    frobenius_square,
    is_frobenius_related,
    is_sidon,
    is_translate,
    two_sided_hypothesis,
)
from bb_lab.group import AbelianGroup
from bb_lab.poly import Poly

G66 = AbelianGroup((6, 6))
G36 = AbelianGroup((3, 6))


def _p(s, G=G66):
    return Poly.from_string(s, G)


# --------------------------------------------------------------- gross anchor
def test_gross_satisfies_all_predicates():
    A, B = _p("x^3 + y + y^2"), _p("y^3 + x + x^2")
    h = two_sided_hypothesis(A, B)
    assert h.d1_A_sidon and h.d1_B_sidon
    assert h.d2_disjoint
    assert h.d3_coord_separated
    assert not h.frobenius_related
    assert h.floor_hypothesis


# ----------------------------------------------------- Frobenius freshman dream
def test_frobenius_square_freshmans_dream():
    B = _p("1 + x + y")
    assert frobenius_square(B) == _p("1 + x^2 + y^2")


def test_frobenius_counterexample_passes_d1_d2_fails_d3():
    A, B = _p("1 + x^2 + y^2"), _p("1 + x + y")
    h = two_sided_hypothesis(A, B)
    assert h.d1_A_sidon and h.d1_B_sidon       # both Sidon (D1 holds)
    assert h.d2_disjoint                       # dA = 2*dB disjoint from dB (D2 holds)
    assert not h.d3_coord_separated            # 0 in x(dA) ∩ x(dB)  (D3 FAILS)
    assert h.frobenius_related                 # A = B^2
    assert not h.floor_hypothesis              # so the 2w floor is NOT guaranteed


def test_frobenius_gate_directional_asymmetry():
    # The gate is an OR over both directions, so as a *gate* it is symmetric:
    B = _p("1 + x + y")
    A = _p("1 + x^2 + y^2")                     # A = B^2
    assert is_frobenius_related(A, B)
    assert is_frobenius_related(B, A) == is_frobenius_related(A, B)

    # ...but the UNDERLYING relation is directional. Here A = B^2 holds, yet B is
    # NOT a translate of A^2 = 1 + x^4 + y^4. Assert each direction separately so
    # the asymmetry is documented, not glossed by the symmetric OR:
    assert frobenius_square(A) == _p("1 + x^4 + y^4")
    assert is_translate(A, frobenius_square(B))         # A is a translate of B^2  -> True
    assert not is_translate(B, frobenius_square(A))     # B is NOT a translate of A^2 -> False
    # the gate fires precisely because the first direction holds.


def test_frobenius_gate_flags_translates_of_the_square():
    B = _p("1 + x + y")
    A_shift = _p("y + x^2*y + y^3")            # y * (1 + x^2 + y^2) = y * B^2
    assert is_translate(A_shift, frobenius_square(B))
    assert is_frobenius_related(A_shift, B)


# ---------------------------------------------------------- [[36,4,4]] anchor
def test_small_doubling_base_fails_d2():
    A, B = _p("x^2 + y + y^3", G36), _p("1 + x + y^2", G36)
    assert is_sidon(A) and is_sidon(B)
    assert not difference_sets_disjoint(A, B)  # D2 fails -> outside the technique
    assert not two_sided_hypothesis(A, B).floor_hypothesis


# ------------------------------------------------------------- unit utilities
def test_is_translate():
    assert is_translate(_p("1 + x + y"), _p("x + x^2 + x*y"))   # shift by x
    assert not is_translate(_p("1 + x + y"), _p("1 + x + y^2"))
    assert not is_translate(_p("1 + x"), _p("1 + x + y"))       # different weight


def test_frobenius_square_with_coordinate_collision():
    # On Z2xZ2 doubling kills everything: (1+x+y)^2 = 1+1+1 = 1 (the three
    # doubled points 0,2x=0,2y=0 all collapse to identity, parity 3 -> {0}).
    G = AbelianGroup((2, 2))
    assert frobenius_square(Poly.from_string("1 + x + y", G)) == Poly.from_string("1", G)
