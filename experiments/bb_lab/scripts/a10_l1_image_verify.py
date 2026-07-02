"""A10 — canonical-grade verification of descent-proper rescue claims.

For a claimed descent-proper rescue (a rescue row outside the
presentation-literal L1-image, `a10_l1_image.py`), independently verify
it at a STRONGER equivalence grade: the cover pair (mapped onto the
product group Z_{2l} x Z_m) is checked against literal axis covers of
ALL moved presentations under full Aut(cover group) x swap x
translation — strictly broader than the group-structured gauge the
image computation uses.  Method: a pair is (that-)equivalent to a
literal lift iff some automorphism image of it fits in a width-l
x-window (after which it IS a literal lift of its windowed reduction),
and the reduction (or its coordinate swap, for y-covers) is a moved
presentation — pure set membership, no canonicalization.

    uv run python scripts/a10_l1_image_verify.py
"""

from __future__ import annotations

import sys
from pathlib import Path

LAB_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LAB_ROOT / "src"))
sys.path.insert(0, str(LAB_ROOT / "scripts"))

from bb_lab.group import AbelianGroup
from bb_lab.poly import Poly
from bb_lab.automorphism import automorphisms as auts_of
from a5_cover_cascade import automorphisms, apply_auto
from a10_descent_covers import CoverGroup, twisted_lift, product_model


def moved_presentations(A: Poly, B: Poly) -> set:
    H = A.group
    ell, m = H.orders
    moved = set()
    for swapped in (False, True):
        P, Q = (B, A) if swapped else (A, B)
        for sigma in automorphisms(ell, m):
            sP, sQ = apply_auto(P, sigma, H), apply_auto(Q, sigma, H)
            for g in H:
                moved.add((frozenset(H.add(g, s) for s in sP.support),
                           frozenset(H.add(g, s) for s in sQ.support)))
    return moved


def in_literal_image(Asupp, Bsupp, ell, m, auts_cover, moved) -> bool:
    two_ell = 2 * ell
    for al in auts_cover:
        for (Sa, Sb) in ((Asupp, Bsupp), (Bsupp, Asupp)):
            Ta = [al(g) for g in Sa]
            Tb = [al(g) for g in Sb]
            xs = {g[0] for g in Ta} | {g[0] for g in Tb}
            for w in range(two_ell):
                if all(((x - w) % two_ell) < ell for x in xs):
                    ra = frozenset((((g[0] - w) % two_ell), g[1]) for g in Ta)
                    rb = frozenset((((g[0] - w) % two_ell), g[1]) for g in Tb)
                    if (ra, rb) in moved:
                        return True
                    sa = frozenset((b, a) for (a, b) in ra)
                    sb = frozenset((b, a) for (a, b) in rb)
                    if (sa, sb) in moved:
                        return True
    return False


def main() -> None:
    H = AbelianGroup((6, 6))
    A = Poly.from_string("y^3 + x + x^2", H)
    B = Poly.from_string("y^5 + x*y + x^2", H)  # hit5 stored
    moved = moved_presentations(A, B)
    G12 = AbelianGroup((12, 6))
    auts12 = auts_of(G12)
    print(f"moved presentations: {len(moved)}; |Aut(Z12xZ6)| = {len(auts12)}")

    Gc = CoverGroup(6, 6, 1, 0)
    Gp, phi = product_model(Gc)
    cases = [
        ("literal control (must be IN)", (0, 0, 0), (0, 0, 0), True),
        ("descent-proper DP1", (0, 0, 0), (0, 0, 1), False),
        ("descent-proper DP2", (0, 0, 0), (0, 1, 1), False),
        ("descent-proper DP3", (0, 0, 1), (0, 0, 0), False),
    ]
    ok = True
    for name, eA, eB, expect_in in cases:
        Ac = frozenset(phi(g) for g in twisted_lift(A, Gc, eA).support)
        Bc = frozenset(phi(g) for g in twisted_lift(B, Gc, eB).support)
        got = in_literal_image(Ac, Bc, 6, 6, auts12, moved)
        status = "PASS" if got == expect_in else "FAIL"
        ok &= got == expect_in
        print(f"{name}: in-image={got} (expected {expect_in}) {status}")
    print("ALL PASS" if ok else "MISMATCH — investigate")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
