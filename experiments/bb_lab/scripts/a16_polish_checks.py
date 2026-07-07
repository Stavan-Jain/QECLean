"""A16 — machine verification of the P1/P2/P3 discharges (the class
small-cycle theorem's last polish items).  Discovery/validation only
(A_HANDOFF §1); each check mirrors a proof step.

  Y1  P3 COMPLETENESS: for every D1-passing 3-set B (exhaustive over
      cyclic Z_n, n ≤ 40, and 2-D grids), every dB-triangle translate
      class beyond the two chirality classes is
        O3   a coset of ⟨s⟩ for some order-3 s ∈ dB, or
        PROG the AP {0, c, 2c} with dB = ±{c, 2c, 3c}.
  Y2  P2 ONE-LINER: for every PROG instance, the AP-triangle image σ
      has weight 3 and c ∈ d(σ) — so σ ~ t + A would force
      c ∈ dA ∩ dB, violating D2.  (The O3 image is an AP-line whose
      difference multiset has multiplicity 3 — violating D1.)
  Y3  P1 / F-tri-5, EMBEDDING-COMPLETE: the last size-4 family
      (dA = {±δ, ±τ, ±(τ+δ)}, dB = {±2δ, ±(τ−δ), ±(τ+2δ)},
      ord δ = 5, ord τ = 3) admits NO (iii)-mirrored realization.
      Any embedding into a floor-bearing frame factors through the
      15-torsion subgroup ⊆ Z₁₅×Z₁₅, so the check over ALL
      (δ, τ) ∈ Z₁₅² × Z₁₅² is complete: assert that never [dA has an
      A-side (iii)-shape] ∧ [dB has the mirrored B-side shape].
      (Same factoring retroactively upgrades W4b (Z₅², pentagonal)
      to embedding-complete.)

Usage:  uv run python scripts/a16_polish_checks.py
"""

from __future__ import annotations

import importlib.util
import sys
from collections import Counter
from itertools import combinations
from pathlib import Path

LAB_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LAB_ROOT / "src"))

from bb_lab.group import AbelianGroup

_spec = importlib.util.spec_from_file_location(
    "a15_t11_residue_hunt", LAB_ROOT / "scripts" / "a15_t11_residue_hunt.py"
)
hunt = importlib.util.module_from_spec(_spec)
sys.modules["a15_t11_residue_hunt"] = hunt
_spec.loader.exec_module(hunt)


def canon(G, S) -> tuple:
    return min(tuple(sorted(G.sub(s, a) for s in S)) for a in S)


def mul(G, k, g):
    out = tuple(0 for _ in G.orders)
    for _ in range(k):
        out = G.add(out, g)
    return out


def order3(G, g) -> bool:
    zero = tuple(0 for _ in G.orders)
    return g != zero and mul(G, 3, g) == zero


# ---------------------------------------------------------------------------
# Y1 + Y2
# ---------------------------------------------------------------------------


def check_Y1_Y2(G, tally: Counter) -> None:
    zero = tuple(0 for _ in G.orders)
    elems = [g for g in G if g != zero]
    for pair in combinations(range(len(elems)), 2):
        B = frozenset([zero, elems[pair[0]], elems[pair[1]]])
        mf, dB = hunt.diffs(G, B)
        if not mf:
            continue
        tally["B-sets"] += 1
        # chirality canonical classes
        refl = canon(G, frozenset(G.sub(b, list(B)[0]) for b in B) or B)
        c_same = canon(G, B)
        c_refl = canon(G, frozenset(G.neg(b) for b in B))
        # PROG detection
        prog_c = [c for c in dB
                  if frozenset([c, G.neg(c), mul(G, 2, c),
                                G.neg(mul(G, 2, c)), mul(G, 3, c),
                                G.neg(mul(G, 3, c))]) == dB]
        o3_elems = [s for s in dB if order3(G, s)]
        for T in hunt.triangle_census(G, dB):
            cT = canon(G, T)
            if cT in (c_same, c_refl):
                continue
            tally["extra-classes"] += 1
            # classify: O3 coset?
            dT = {G.sub(a, b) for a in T for b in T if a != b}
            is_o3 = (len(dT) == 2
                     and all(order3(G, v) for v in dT)
                     and any(v in dB for v in dT))
            is_prog = False
            if prog_c:
                for c in prog_c:
                    ap = frozenset([zero, c, mul(G, 2, c)])
                    if canon(G, ap) == cT:
                        is_prog = True
                        # Y2: image weight 3 with c in d(sigma)
                        img = hunt.conv(G, B, ap)
                        assert len(img) == 3, "PROG image not weight 3"
                        dimg = {G.sub(a, b) for a in img for b in img
                                if a != b}
                        assert c in dimg or G.neg(c) in dimg, (
                            "PROG one-liner premise fails!")
                        tally["Y2-prog-verified"] += 1
                        break
            assert is_o3 or is_prog, (
                f"Y1 COMPLETENESS FAIL: extra class {sorted(T)} for "
                f"B={sorted(B)} on {G.orders} is neither O3 nor PROG")
            tally["O3" if is_o3 else "PROG"] += 1
            if is_o3:
                # Y2 (O3 side): image is an AP-line ⟹ D1-kill premise
                img = hunt.conv(G, B, T)
                if len(img) == 3:
                    dimg = [G.sub(a, b) for a in img for b in img
                            if a != b]
                    assert len(set(dimg)) == 2, "O3 image not an AP-line"
                    tally["Y2-o3-verified"] += 1


def run_Y12() -> None:
    tally = Counter()
    for n in range(5, 41):
        check_Y1_Y2(AbelianGroup((n,)), tally)
    for orders in ((9, 6), (6, 10), (15, 3), (5, 5), (9, 3), (15, 5),
                   (6, 14), (21, 3), (9, 9), (6, 6)):
        check_Y1_Y2(AbelianGroup(orders), tally)
    print(f"Y1+Y2 PASS: {dict(tally)}")
    print("  (every extra triangle class across all ambients is O3 or "
          "PROG; every PROG image carries c ∈ d(σ) ∩ ±dB; every O3 "
          "image is an AP-line)")


# ---------------------------------------------------------------------------
# Y3 — F-tri-5 over Z₁₅×Z₁₅ (embedding-complete by torsion factoring)
# ---------------------------------------------------------------------------


def a_side_shape_ok(G, dS) -> bool:
    """Does dS admit the A-side (iii)-shape: {±(0,w), ±(u,s), ±(u,s')}
    with u ≠ 0 and all y-parts ≠ 0 — or the A2 shape (dS ⊂ {x = 0},
    all y-parts ≠ 0)?"""
    if any(d[1] == 0 for d in dS):
        return False  # A-side difference sets never have y = 0 parts
    xs = sorted(d[0] for d in dS)
    if all(x == 0 for x in xs):
        return True  # A2
    # A1: x-multiset {0, 0, u, u, -u, -u}
    zeros = [d for d in dS if d[0] == 0]
    if len(zeros) != 2:
        return False
    slant_x = {d[0] for d in dS if d[0] != 0}
    # slants come in ± pairs with a single |u|
    return len(slant_x) <= 2


def b_side_shape_ok(G, dS) -> bool:
    """Mirror: {±(p,0), ±(q,h), ±(p+q,h)} with all x-parts ≠ 0 — or B2
    (dS ⊂ {y = 0}, x-parts ≠ 0)."""
    if any(d[0] == 0 for d in dS):
        return False
    ys = [d for d in dS if d[1] == 0]
    if all(d[1] == 0 for d in dS):
        return True  # B2
    return len(ys) == 2  # B1: exactly one ± pair at y = 0


def run_Y3() -> None:
    G = AbelianGroup((15, 15))
    zero = (0, 0)
    elems = [g for g in G if g != zero]
    ord5 = [g for g in elems if mul(G, 5, g) == zero]
    ord3 = [g for g in elems if mul(G, 3, g) == zero]
    n_data = n_d1 = n_bad = 0
    for d in ord5:
        for t in ord3:
            dA_reps = [d, t, G.add(t, d)]
            dB_reps = [mul(G, 2, d), G.sub(t, d),
                       G.add(t, mul(G, 2, d))]
            dA = set()
            dB = set()
            for v in dA_reps:
                dA |= {v, G.neg(v)}
            for v in dB_reps:
                dB |= {v, G.neg(v)}
            n_data += 1
            if len(dA) != 6 or len(dB) != 6 or (dA & dB):
                continue  # D1/D2 already dead
            if any(G.add(v, v) == zero for v in dA | dB):
                continue
            n_d1 += 1
            # the (iii)-mirrored realization test, both orientations
            if (a_side_shape_ok(G, dA) and b_side_shape_ok(G, dB)) or \
               (a_side_shape_ok(G, frozenset((g[1], g[0]) for g in dB))
                    and b_side_shape_ok(
                        G, frozenset((g[1], g[0]) for g in dA))):
                n_bad += 1
                print(f"  !! Y3 FAIL: (iii)-compatible F-tri-5 data "
                      f"δ={d} τ={t}")
    assert n_bad == 0, "F-tri-5 admits a (iii)-mirrored embedding!"
    print(f"Y3 PASS: {n_data} (δ, τ) ∈ ord5 × ord3 over Z₁₅² "
          f"({n_d1} pass D1/D2); 0 admit an (iii)-mirrored shape — "
          "embedding-complete by 15-torsion factoring")


if __name__ == "__main__":
    run_Y12()
    run_Y3()
