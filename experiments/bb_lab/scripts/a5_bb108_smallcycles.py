"""A5 (goal 2) — confirmation script for the bb_108 small-cycle template run.

The hand argument (notes/A5_goal2_log.md, Entry 2) runs the A4 §4 case
grid on bb_108 = (Z₉×Z₆, A = x³+y+y², B = y³+x+x²) and concludes:

    no nonzero 1-cycle (either side) of weight ≤ 5; hence d(bb_108) ≥ 6,
    and the one-sided annihilator floors are μ(Ann A) = μ(Ann B) = 12.

Every check below CONFIRMS a step of the hand argument (per the A_HANDOFF
§1 constraint, none of these numbers is load-bearing; the argument is the
prose + the surveyable tables it cites):

  W1  frame + component table: Z₂ layer frame, radical components are
      c·(1+s) with the radical orbit sets W_A, W_B factoring through Z₃².
  W2  the Z₂-engine: Ann(A) = (1+s)⊗I(W_A) (dimension + membership),
      min weight 12 = 2·3·d₃(three-orbit row), attained.  Mirror for B.
  W3  (PAR) + difference sets: |A|,|B| odd; dA, dB multiplicity-free,
      dA ∩ dB = ∅ (x-coordinate-disjoint, in fact).
  W4  (1,1): no translate coincidence A·g = B·r.
  W5  (1,3)/(3,1): triangle census — the dB-triangles with weight-3
      image give constant-y images (incompatible with A·g's three
      distinct y's); mirror for dA-triangles (constant-x vs B·r).
  W6  (2,2): exhaustive — no cycle with |u_L| = |u_R| = 2.
  W7  exhaustive small-cycle confirmation: SAT-UNSAT at weights 1..5
      for both H_X and H_Z kernels (nonzero vector, weight ≤ 5).

Usage:  uv run python scripts/a5_bb108_smallcycles.py
"""

from __future__ import annotations

import sys
from itertools import combinations
from pathlib import Path

LAB_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LAB_ROOT / "src"))
sys.path.insert(0, str(LAB_ROOT / "scripts"))

import numpy as np

from bb_lab.checks import bb_check_matrices
from bb_lab.group import AbelianGroup
from bb_lab.linalg import nullspace_f2, rank_f2
from bb_lab.poly import Poly
from bb_lab.sat_distance import _solve_at_weight

import importlib.util

_spec = importlib.util.spec_from_file_location(
    "a5_instance_hypotheses", LAB_ROOT / "scripts" / "a5_instance_hypotheses.py"
)
a5 = importlib.util.module_from_spec(_spec)
sys.modules["a5_instance_hypotheses"] = a5
_spec.loader.exec_module(a5)

ELL, M = 9, 6
G = AbelianGroup((ELL, M))
A = Poly.from_string("x^3 + y + y^2", G)
B = Poly.from_string("y^3 + x + x^2", G)

PASS, FAIL = "PASS", "FAIL"
failures: list[str] = []


def report(tag: str, ok: bool, detail: str = "") -> None:
    print(f"  [{tag}] {'PASS' if ok else 'FAIL'}  {detail}")
    if not ok:
        failures.append(tag)


# ---------------------------------------------------------------------------
# group-algebra convolution helpers (support arithmetic mod 2)
# ---------------------------------------------------------------------------


def conv(p: frozenset, q: frozenset) -> frozenset:
    counts: dict[tuple[int, ...], int] = {}
    for a in p:
        for b in q:
            c = G.add(a, b)
            counts[c] = counts.get(c, 0) + 1
    return frozenset(c for c, k in counts.items() if k % 2)


def translate(p: frozenset, t: tuple[int, ...]) -> frozenset:
    return frozenset(G.add(a, t) for a in p)


# ===========================================================================
print("== W1: frame and component table")
rep = a5.check_instance("bb_108", ELL, M, "x^3 + y + y^2", "y^3 + x + x^2")
report("W1.frame", rep.frame.shape == "Z2", f"frame = {rep.frame.shape}")

# radical orbit sets; expected from the checker run (Entry 2 table)
W_A_expected = {(0, 1), (3, 1), (3, 2)}
W_B_expected = {(3, 0), (3, 1), (3, 2)}
rad_A = {c.orbit_rep for c in rep.comps_A if c.kind == a5.RADICAL_OTHER}
rad_B = {c.orbit_rep for c in rep.comps_B if c.kind == a5.RADICAL_OTHER}
zero_A = [c for c in rep.comps_A if c.kind == a5.ZERO]
zero_B = [c for c in rep.comps_B if c.kind == a5.ZERO]
report("W1.radical_sets", rad_A == W_A_expected and rad_B == W_B_expected,
       f"W_A = {sorted(rad_A)}, W_B = {sorted(rad_B)}")
report("W1.no_zero_components", not zero_A and not zero_B)
# each radical component is c·(1+s): the two layer values are equal & nonzero
rigid = all(
    c.value_vector[0] == c.value_vector[1] and any(c.value_vector[0])
    for c in rep.comps_A + rep.comps_B
    if c.kind == a5.RADICAL_OTHER
)
report("W1.radicals_are_c_times_u", rigid)
# every radical-orbit character factors through Z₃² (x-component ∈ {0,3,6},
# i.e. rep x ∈ {0,3}; y-component arbitrary mod 3)
factors = all(k[0] % 3 == 0 for k in (rad_A | rad_B))
report("W1.radical_orbits_factor_through_Z3sq", factors)

# ===========================================================================
print("== W2: the Z₂-engine — Ann(A) = (1+s)⊗I(W_A), min weight 12")
# circulant convolution matrices on F₂[Z₉×Z₆] (n = 54)
elems = list(G)
idx = {g: i for i, g in enumerate(elems)}
n = len(elems)


def conv_matrix(p: Poly) -> np.ndarray:
    Mx = np.zeros((n, n), dtype=np.uint8)
    for g in elems:
        for a in p.support:
            Mx[idx[G.add(g, a)], idx[g]] ^= 1
    return Mx


for name, P, W_exp in [("A", A, W_A_expected), ("B", B, W_B_expected)]:
    MP = conv_matrix(P)
    ann_dim = n - rank_f2(MP)
    # I(W): ideal of F₂[Z₉×Z₃] with Fourier support ⊆ W; dim = Σ|orbit| = 6
    # (1+s)⊗I(W) has the same dim.  Structure theorem ⟹ dim Ann = 6.
    report(f"W2.dim_Ann_{name}", ann_dim == 6, f"dim Ann({name}) = {ann_dim}")
    # min weight over the full annihilator (dim 6 ⟹ 63 nonzero elements)
    basis = nullspace_f2(MP)
    best, best_v = n + 1, None
    for mask in range(1, 2 ** basis.shape[0]):
        v = np.zeros(n, dtype=np.uint8)
        mm, i = mask, 0
        while mm:
            if mm & 1:
                v ^= basis[i]
            mm >>= 1
            i += 1
        w = int(v.sum())
        if 0 < w < best:
            best, best_v = w, v
    report(f"W2.minwt_Ann_{name}", best == 12, f"μ(Ann {name}) = {best}")
    # every annihilator element is (1+s)-periodic: v(x, y) = v(x, y+3)
    ok_period = True
    for mask in range(1, 2 ** basis.shape[0]):
        v = np.zeros(n, dtype=np.uint8)
        mm, i = mask, 0
        while mm:
            if mm & 1:
                v ^= basis[i]
            mm >>= 1
            i += 1
        for g in elems:
            if v[idx[g]] != v[idx[G.add(g, (0, 3))]]:
                ok_period = False
                break
        if not ok_period:
            break
    report(f"W2.Ann_{name}_is_u_tensor", ok_period,
           "every element (0,3)-periodic = (1+s)⊗I form")

# ===========================================================================
print("== W3: (PAR) + difference sets")
report("W3.parity", len(A.support) % 2 == 1 and len(B.support) % 2 == 1,
       f"|A| = {len(A.support)}, |B| = {len(B.support)}")
d = rep.diff
report("W3.mult_free", d.dA_mult_free and d.dB_mult_free,
       f"|dA| = {len(d.dA)}, |dB| = {len(d.dB)}")
report("W3.disjoint", d.disjoint, f"coord-disjoint = {d.coord_disjoint}")

# ===========================================================================
print("== W4: split (1,1) — no translate coincidence")
hit = any(conv(A.support, frozenset([g])) == conv(B.support, frozenset([(0, 0)]))
          for g in elems)
report("W4.no_coincidence", not hit)

# ===========================================================================
print("== W5: splits (1,3)/(3,1) — triangle census and kills")


def triangle_census(dS: frozenset) -> list[frozenset]:
    """Translation classes {0, a, b} with a, b, b−a ∈ dS."""
    classes: set[frozenset] = set()
    for a in dS:
        for b in dS:
            if a == b:
                continue
            if G.sub(b, a) in dS:
                tri = frozenset([(0, 0), a, b])
                # canonicalize by translation: lexicographically smallest image
                cands = [frozenset(G.sub(t, mn) for t in tri) for mn in tri]
                classes.add(min(cands, key=lambda s: sorted(s)))
    return sorted(classes, key=lambda s: sorted(s))


def y_coords(s: frozenset) -> set[int]:
    return {c[1] for c in s}


def x_coords(s: frozenset) -> set[int]:
    return {c[0] for c in s}


def is_translate_of(img: frozenset, P: Poly) -> bool:
    return any(translate(P.support, t) == img for t in elems)


def profile(img: frozenset) -> str:
    """Surveyable shape data: distinct-x / distinct-y counts."""
    return f"#x={len(x_coords(img))},#y={len(y_coords(img))}"


# (1,3): u_L = {g}, u_R = triangle z; B·z must be a TRANSLATE OF A.
# (Gross's kill — const-y image vs A's three distinct y's — is the special
# case; the principled per-class check is the direct translate comparison.)
tris_B = triangle_census(d.dB)
ok13 = True
detail13 = []
for tri in tris_B:
    img = conv(B.support, tri)
    w = len(img)
    if w == 3:
        hit = is_translate_of(img, A)
        detail13.append(f"{sorted(tri)} → wt 3 [{profile(img)}], ≅A:{hit}")
        if hit:
            ok13 = False
    else:
        detail13.append(f"{sorted(tri)} → wt {w} ≠ 3")
report("W5.dB_triangles", ok13,
       f"{len(tris_B)} classes: " + "; ".join(detail13))
# the surveyable reasons: A has 3 distinct y's; B-translates have 3 distinct x's
ok_Ay = len(y_coords(A.support)) == 3
report("W5.A_three_distinct_y", ok_Ay)

# (3,1) mirror: u_R = {r}, u_L = triangle z; A·z must be a TRANSLATE OF B.
tris_A = triangle_census(d.dA)
ok31 = True
detail31 = []
for tri in tris_A:
    img = conv(A.support, tri)
    w = len(img)
    if w == 3:
        hit = is_translate_of(img, B)
        detail31.append(f"{sorted(tri)} → wt 3 [{profile(img)}], ≅B:{hit}")
        if hit:
            ok31 = False
    else:
        detail31.append(f"{sorted(tri)} → wt {w} ≠ 3")
report("W5.dA_triangles", ok31,
       f"{len(tris_A)} classes: " + "; ".join(detail31))
ok_Bx = len(x_coords(B.support)) == 3
report("W5.B_three_distinct_x", ok_Bx)

# ===========================================================================
print("== W6: split (2,2) — exhaustive")
# translation-invariance: fix 0 ∈ u_L.  u_L = {0, dl}, u_R = {t, t+dr}.
found22 = []
nonzero = [g for g in elems if g != (0, 0)]
for dl in nonzero:
    sigL = conv(A.support, frozenset([(0, 0), dl]))
    if not sigL:
        continue
    for dr in nonzero:
        base = conv(B.support, frozenset([(0, 0), dr]))
        if len(base) != len(sigL):
            continue
        for t in elems:
            if translate(base, t) == sigL:
                found22.append((dl, dr, t))
report("W6.no_22_cycles", not found22, f"matches: {found22[:3]}")

# ===========================================================================
print("== W7: exhaustive small-cycle confirmation (SAT, w = 1..5)")
checks = bb_check_matrices(A, B)
for nm, H in [("H_X", checks.H_X), ("H_Z", checks.H_Z)]:
    L_any = np.eye(H.shape[1], dtype=np.uint8)  # "some coordinate is 1" ⇔ x ≠ 0
    ok = True
    for w in range(1, 6):
        witness, _ = _solve_at_weight(H, L_any, w)
        if witness is not None:
            ok = False
            report(f"W7.{nm}", False,
                   f"weight-{int(witness.sum())} kernel vector exists!")
            break
    if ok:
        report(f"W7.{nm}", True, "no nonzero kernel vector of weight ≤ 5")

# ===========================================================================
print()
if failures:
    print(f"FAILURES: {failures}")
    sys.exit(1)
print("ALL CHECKS PASS — the bb_108 small-cycle hand argument is confirmed.")
print("Conclusion (analytic, confirmed): no nonzero 1-cycle of weight ≤ 5;")
print("d(bb_108) ≥ 6; μ(Ann A) = μ(Ann B) = 12 (attained).")
