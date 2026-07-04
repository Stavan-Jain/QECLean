"""A5 (goal 2) — confirmation script for the bb_90 small-cycle template run.

The hand argument (notes/A5_goal2_log.md, Entry 4) runs the A4 §4 case
grid on bb_90 = (Z₁₅×Z₃, A = x⁹+y+y², B = 1+x²+x⁷) — the SEMISIMPLE
frame (|G| odd, no 2-part at all) — and concludes:

    no nonzero 1-cycle (either side) of weight ≤ 5; hence d(bb_90) ≥ 6,
    and μ(Ann A) = μ(Ann B) = 10 (attained).

The semisimple engine replaces A4 §3: Ann(A) = I(V_A) (the ideal of
the vanishing-orbit set), and bb_90's vanishing characters all have
order 3, factoring through Q = Z₃² with kernel K ≅ Z₅ — so
μ(Ann) = 5·d₃((3,F)) = 10 by the gross d₃ dictionary, pulled back the
same way bb_108's Z₂-frame floor was (there 3-fold through Z₉×Z₃→Z₃²,
here 5-fold through Z₁₅×Z₃→Z₃²).

Checks (all confirmation-only, per A_HANDOFF §1):

  W1  frame semisimple; vanishing-orbit sets V_A, V_B; every vanishing
      character has order 3 (factors through Z₃²).
  W2  Ann(A) = I(V_A): dim 6, μ = 10 attained, K-periodicity
      (every annihilator element satisfies v(x,y) = v(x+3,y)).
  W3  (PAR) + difference sets: |A|,|B| odd; dA, dB mult-free,
      dA ∩ dB = ∅; structurally dB ⊂ {y=0}, dA ⊂ {y ∈ {1,2}}.
  W4  (1,1): no translate coincidence.
  W5  (1,3): dB-triangles are constant-y (dB lives in the y=0 line),
      and π_y kills: π_y(B·z) has weight 1 vs π_y(A·g) = 1+y+y²
      weight 3.  (3,1): census-free π_y kill —
      (1+y+y²)·v = ε(v)·(1+y+y²) in F₂[Z₃], so π_y(A·z) has weight 3
      for ANY odd-size z, while π_y(B·r) = y^{r_y} has weight 1.
  W6  (2,2): π_y forces the r-pair y-gap to 0; then π_x weights
      mismatch (left x⁹(1+x^g): weight ∈ {0,2}; right
      (1+x²+x⁷)(1+x^g): weight ∈ {4,6} for g ≠ 0).  Exhaustive
      confirmation that no (2,2) cycle exists.
  W7  exhaustive small-cycle confirmation: SAT-UNSAT at weights 1..5
      for both H_X and H_Z kernels.

Usage:  uv run python scripts/a5_bb90_smallcycles.py
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

LAB_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LAB_ROOT / "src"))

import numpy as np

from bb_lab.checks import bb_check_matrices
from bb_lab.group import AbelianGroup
from bb_lab.linalg import nullspace_f2, rank_f2
from bb_lab.poly import Poly
from bb_lab.sat_distance import _solve_at_weight

_spec = importlib.util.spec_from_file_location(
    "a5_instance_hypotheses", LAB_ROOT / "scripts" / "a5_instance_hypotheses.py"
)
a5 = importlib.util.module_from_spec(_spec)
sys.modules["a5_instance_hypotheses"] = a5
_spec.loader.exec_module(a5)

ELL, M = 15, 3
G = AbelianGroup((ELL, M))
A = Poly.from_string("x^9 + y + y^2", G)
B = Poly.from_string("1 + x^2 + x^7", G)

failures: list[str] = []


def report(tag: str, ok: bool, detail: str = "") -> None:
    print(f"  [{tag}] {'PASS' if ok else 'FAIL'}  {detail}")
    if not ok:
        failures.append(tag)


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
print("== W1: semisimple frame and vanishing orbits")
rep = a5.check_instance("bb_90", ELL, M, "x^9 + y + y^2", "1 + x^2 + x^7")
report("W1.frame", rep.frame.shape == "semisimple",
       f"frame = {rep.frame.shape}")
V_A_expected = {(0, 1), (5, 1), (5, 2)}
V_B_expected = {(5, 0), (5, 1), (5, 2)}
V_A = {c.orbit_rep for c in rep.comps_A if c.kind == a5.ZERO}
V_B = {c.orbit_rep for c in rep.comps_B if c.kind == a5.ZERO}
report("W1.vanishing_sets", V_A == V_A_expected and V_B == V_B_expected,
       f"V_A = {sorted(V_A)}, V_B = {sorted(V_B)}")
# no radical components at all; everything else is a unit
kinds = {c.kind for c in rep.comps_A + rep.comps_B}
report("W1.units_or_zero_only", kinds <= {a5.UNIT, a5.ZERO}, f"kinds = {kinds}")
# every vanishing character has order 3 (x-component ∈ {0,5,10}, i.e.
# rep x ∈ {0,5}) — factors through Q = Z₃² via (x mod 3 ↔ x·(1/5), y)
factors = all(k[0] % 5 == 0 for k in (V_A | V_B))
report("W1.vanishing_orbits_factor_through_Z3sq", factors)

# ===========================================================================
print("== W2: semisimple engine — Ann = I(V), μ = 10, K-periodicity")
elems = list(G)
idx = {g: i for i, g in enumerate(elems)}
n = len(elems)


def conv_matrix(p: Poly) -> np.ndarray:
    Mx = np.zeros((n, n), dtype=np.uint8)
    for g in elems:
        for a in p.support:
            Mx[idx[G.add(g, a)], idx[g]] ^= 1
    return Mx


for name, P in [("A", A), ("B", B)]:
    MP = conv_matrix(P)
    ann_dim = n - rank_f2(MP)
    report(f"W2.dim_Ann_{name}", ann_dim == 6, f"dim Ann({name}) = {ann_dim}")
    basis = nullspace_f2(MP)
    best = n + 1
    ok_period = True
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
            best = w
        for g in elems:
            if v[idx[g]] != v[idx[G.add(g, (3, 0))]]:
                ok_period = False
                break
    report(f"W2.minwt_Ann_{name}", best == 10, f"μ(Ann {name}) = {best}")
    report(f"W2.Ann_{name}_K_periodic", ok_period,
           "every element (3,0)-periodic = 5-fold pullback from Z₃²")

# ===========================================================================
print("== W3: (PAR) + difference sets")
report("W3.parity", len(A.support) % 2 == 1 and len(B.support) % 2 == 1)
d = rep.diff
report("W3.mult_free", d.dA_mult_free and d.dB_mult_free,
       f"|dA| = {len(d.dA)}, |dB| = {len(d.dB)}")
report("W3.disjoint", d.disjoint, f"coord-disjoint = {d.coord_disjoint}")
report("W3.dB_in_y0_line", all(t[1] == 0 for t in d.dB),
       f"dB = {sorted(d.dB)}")
report("W3.dA_y_nonzero", all(t[1] != 0 for t in d.dA),
       f"dA y-coords = {sorted({t[1] for t in d.dA})}")

# ===========================================================================
print("== W4: split (1,1) — no translate coincidence")
hit = any(translate(A.support, g) == B.support for g in elems)
report("W4.no_coincidence", not hit)

# ===========================================================================
print("== W5: splits (1,3)/(3,1) — projection kills")


def triangle_census(dS: frozenset) -> list[frozenset]:
    classes: set[frozenset] = set()
    for a in dS:
        for b in dS:
            if a == b:
                continue
            if G.sub(b, a) in dS:
                tri = frozenset([(0, 0), a, b])
                cands = [frozenset(G.sub(t, mn) for t in tri) for mn in tri]
                classes.add(min(cands, key=lambda s: sorted(s)))
    return sorted(classes, key=lambda s: sorted(s))


def proj_y(s: frozenset) -> frozenset:
    counts: dict[int, int] = {}
    for c in s:
        counts[c[1]] = counts.get(c[1], 0) + 1
    return frozenset(y for y, k in counts.items() if k % 2)


# (1,3): every dB-triangle is constant-y (structural), so B·z is
# constant-y with π_y weight ≤ 1, while π_y(A·g) = 1+y+y² (weight 3).
tris_B = triangle_census(d.dB)
ok_const = all(len({c[1] for c in tri}) == 1 for tri in tris_B)
report("W5.dB_triangles_constant_y", ok_const,
       f"{len(tris_B)} classes, all in one y-row")
ok_no_translate = all(
    len(conv(B.support, tri)) != 3
    or all(translate(A.support, t) != conv(B.support, tri) for t in elems)
    for tri in tris_B
)
report("W5.dB_triangle_images_not_A", ok_no_translate)
# π_y(A·g) = 1+y+y² for every g
ok_Ay = proj_y(A.support) == frozenset({0, 1, 2})
report("W5.proj_y_A_full", ok_Ay, f"π_y(A) = {sorted(proj_y(A.support))}")

# (3,1) census-free kill: (1+y+y²)·v = ε(v)·(1+y+y²) in F₂[Z₃] —
# verified over all 8 elements v; hence π_y(A·z) = 1+y+y² (weight 3)
# for any odd-|z|, while π_y(B·r) = y^{r_y} (weight 1, π_y(B) = 1).
ZY = AbelianGroup((3,))
all_ones = frozenset({(0,), (1,), (2,)})
ok_alg = True
for mask in range(8):
    v = frozenset((i,) for i in range(3) if (mask >> i) & 1)
    prod_counts: dict[tuple[int, ...], int] = {}
    for a in all_ones:
        for b in v:
            c = ZY.add(a, b)
            prod_counts[c] = prod_counts.get(c, 0) + 1
    prod = frozenset(c for c, k in prod_counts.items() if k % 2)
    expected = all_ones if len(v) % 2 else frozenset()
    if prod != expected:
        ok_alg = False
report("W5.ones_absorption_in_F2Z3", ok_alg,
       "(1+y+y²)·v = ε(v)(1+y+y²) for all v")
report("W5.proj_y_B_monomial", proj_y(B.support) == frozenset({0}),
       f"π_y(B) = {sorted(proj_y(B.support))}")

# ===========================================================================
print("== W6: split (2,2) — projection weights + exhaustive")
# right-side π_x weight table: (1+x²+x⁷)(1+x^g) over Z₁₅, g ≠ 0
ZX = AbelianGroup((15,))
Bx = frozenset({(0,), (2,), (7,)})
ok_tbl = True
weights = {}
for g in range(1, 15):
    pair = frozenset({(0,), (g,)})
    counts: dict[tuple[int, ...], int] = {}
    for a in Bx:
        for b in pair:
            c = ZX.add(a, b)
            counts[c] = counts.get(c, 0) + 1
    w = sum(1 for k in counts.values() if k % 2)
    weights[g] = w
    if w < 4:
        ok_tbl = False
report("W6.right_px_weight_table", ok_tbl,
       f"(1+x²+x⁷)(1+x^g) weights: {sorted(set(weights.values()))} (all ≥ 4)")
# exhaustive: no (2,2) cycle (0 ∈ u_L fixed by translation)
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
    L_any = np.eye(H.shape[1], dtype=np.uint8)
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
print("ALL CHECKS PASS — the bb_90 small-cycle hand argument is confirmed.")
print("Conclusion (analytic, confirmed): no nonzero 1-cycle of weight ≤ 5;")
print("d(bb_90) ≥ 6; μ(Ann A) = μ(Ann B) = 10 (attained).")
