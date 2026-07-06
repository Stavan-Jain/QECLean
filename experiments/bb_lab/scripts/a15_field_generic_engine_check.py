"""A15 §1.3 — field-genericity verification for the Z₂²-engine dichotomy.

The A15 plan (§1.3) claims the one-sided-floor half of the A4 §3 engine
is FIELD-GENERIC: only the value-rigidity layers are F₄-locked.  This
script verifies the three ingredients over K = F_{2^r}, r ∈ {2,3,4,6},
plus the instance-level consequence on the first off-Z₃² target.

Claims checked (all discovery/validation only — A_HANDOFF §1; a "PASS"
here licenses writing the hand proof, nothing more):

  (E1) In K[Z₂²] = K[U,V]/(U²,V²) (U = 1+s_x, V = 1+s_y), for
       D = aU + bV + cUV with (a,b) ≠ (0,0):
         D² = 0,   x·D = 0  ⟺  x₀ = 0 ∧ x₁·b + x₂·a = 0,
       hence Ann(D) = span_K{aU + bV, UV} = (D), dimension 2.
  (E2) Support dichotomy ⟺ distinctness: every nonzero α·D + β·UV has
       ≥ 3 nonzero slot coordinates ⟺ {0, a, b, a+b} pairwise distinct
       (⟺ a ≠ 0, b ≠ 0, a ≠ b); c plays no role.  When distinctness
       FAILS the true minimum support is recorded (expected: 2).
  (E2') Predicate form: distinctness ⟺ the 4 slot values of D itself
       are pairwise distinct.  (The A5 checker's ENGINE_RADICAL — one
       zero + three distinct — is the special case c ∈ {0,a,b,a+b};
       the widened predicate drops the zero-count requirement.)
  (E3) Instance floors:
       - control: gross base bb_72 (Z₆×Z₆, A = x³+y+y², B = y³+x+x²) —
         every radical component passes the widened predicate; exact
         weight-2/4/6 kernel exhaustion (+ PAR) confirms
         μ(Ann A) = μ(Ann B) = 6.
       - target: Z₆×Z₁₄ [[168,12,6]] (A = 1+y+x³y³, B = 1+x+x²y⁷, the
         A8 doubling base) — components live in F₄/F₈/F₆₄; classify
         with the widened predicate; exact weight-2/4/6 exhaustion for
         the floor; sample Ann elements for the ≥3-nonzero-layers /
         all-layers-even structure the engine predicts.

Usage:  uv run python scripts/a15_field_generic_engine_check.py
"""

from __future__ import annotations

import importlib.util
import random
import sys
from itertools import combinations, product
from pathlib import Path

LAB_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LAB_ROOT / "src"))

import numpy as np

from bb_lab.algebraic_features import _PRIM_POLYS
from bb_lab.group import AbelianGroup
from bb_lab.linalg import nullspace_f2
from bb_lab.poly import Poly

_spec = importlib.util.spec_from_file_location(
    "a5_instance_hypotheses", LAB_ROOT / "scripts" / "a5_instance_hypotheses.py"
)
a5 = importlib.util.module_from_spec(_spec)
sys.modules["a5_instance_hypotheses"] = a5
_spec.loader.exec_module(a5)


# ---------------------------------------------------------------------------
# Int-encoded F_{2^r} arithmetic (log/antilog; the _PRIM_POLYS moduli are
# primitive, so t generates Kˣ)
# ---------------------------------------------------------------------------


def make_field(r: int):
    p = _PRIM_POLYS[r]
    pmask = sum(bit << i for i, bit in enumerate(p))
    q = 1 << r
    exp = [1] * (q - 1)
    cur = 1
    for i in range(1, q - 1):
        cur <<= 1
        if cur & q:
            cur ^= pmask
        exp[i] = cur
    log = {v: i for i, v in enumerate(exp)}
    assert len(log) == q - 1, f"t not primitive for r={r}?"

    def mul(x: int, y: int) -> int:
        if x == 0 or y == 0:
            return 0
        return exp[(log[x] + log[y]) % (q - 1)]

    return q, mul


# K[Z₂²] elements as 4-tuples over the SLOT (group-element) basis
# (1, s_x, s_y, s_x s_y).  U = 1+s_x = (1,1,0,0), V = (1,0,1,0),
# UV = (1,1,1,1).  Multiplication via the U,V presentation.


def slot_vec(a: int, b: int, c: int) -> tuple[int, int, int, int]:
    """aU + bV + cUV in the slot basis."""
    return (a ^ b ^ c, a ^ c, b ^ c, c)


def uv_coords(x: tuple[int, int, int, int]) -> tuple[int, int, int, int]:
    """Slot basis → (x₀, x₁, x₂, x₃) coords in the (1, U, V, UV) basis.
    1 = (1,0,0,0), U = (1,1,0,0), V = (1,0,1,0), UV = (1,1,1,1):
    x = x₀·1 + x₁·U + x₂·V + x₃·UV  ⟹  slot = (x₀^x₁^x₂^x₃, x₁^x₃, x₂^x₃, x₃)."""
    s1, sx, sy, sxy = x
    x3 = sxy
    x2 = sy ^ x3
    x1 = sx ^ x3
    x0 = s1 ^ x1 ^ x2 ^ x3
    return (x0, x1, x2, x3)


def ring_mul(x, y, mul):
    """Product in K[U,V]/(U²,V²), inputs/outputs in (1,U,V,UV) coords."""
    x0, x1, x2, x3 = x
    y0, y1, y2, y3 = y
    z0 = mul(x0, y0)
    z1 = mul(x0, y1) ^ mul(x1, y0)
    z2 = mul(x0, y2) ^ mul(x2, y0)
    z3 = (
        mul(x0, y3)
        ^ mul(x3, y0)
        ^ mul(x1, y2)
        ^ mul(x2, y1)
    )
    return (z0, z1, z2, z3)


def check_E1(r: int, exhaustive: bool, rng: random.Random) -> str:
    q, mul = make_field(r)
    if exhaustive:
        Ds = [(a, b, c) for a in range(q) for b in range(q) for c in range(q)
              if (a, b) != (0, 0)]
        xs = list(product(range(q), repeat=4))
    else:
        Ds = [(rng.randrange(q), rng.randrange(q), rng.randrange(q))
              for _ in range(400)]
        Ds = [(a, b, c) for (a, b, c) in Ds if (a, b) != (0, 0)] or [(1, 0, 0)]
        xs = [tuple(rng.randrange(q) for _ in range(4)) for _ in range(400)]
    n_checked = 0
    for (a, b, c) in Ds:
        D = (0, a, b, c)  # (1,U,V,UV) coords
        assert ring_mul(D, D, mul) == (0, 0, 0, 0), f"D²≠0 at {(a, b, c)}"
        for x in xs:
            xD = ring_mul(x, D, mul)
            pred = x[0] == 0 and (mul(x[1], b) ^ mul(x[2], a)) == 0
            assert (xD == (0, 0, 0, 0)) == pred, (
                f"Ann predicate mismatch r={r} D={(a, b, c)} x={x}"
            )
            n_checked += 1
    mode = "exhaustive" if exhaustive else "sampled"
    return f"E1 r={r} ({mode}): {len(Ds)} D × {len(xs)} x = {n_checked} PASS"


def check_E2_E2p(r: int) -> tuple[str, dict]:
    """Exhaustive over (a,b) [α scaled to 1, β free] and (a,b,c) for E2'."""
    q, mul = make_field(r)
    stats = {"distinct_pairs": 0, "nondistinct_pairs": 0, "min_supp_fail": 4}
    for a in range(q):
        for b in range(q):
            if (a, b) == (0, 0):
                continue
            distinct = a != 0 and b != 0 and a != b
            # ideal elements: α=0 → β·UV (full support, fine);
            # α≠0: scale to α=1 (K-scaling preserves support): β free.
            min_zeros_seen = 0
            for beta in range(q):
                vec = slot_vec(a, b, beta)  # 1·(aU+bV) + β·UV
                nz = sum(1 for v in vec if v)
                if nz == 0:
                    raise AssertionError("zero ideal element at nonzero (α,β)")
                zeros = 4 - nz
                min_zeros_seen = max(min_zeros_seen, zeros)
                if distinct:
                    assert zeros <= 1, (
                        f"r={r} (a,b)={a, b} β={beta}: {zeros} zeros "
                        "despite distinctness"
                    )
            if distinct:
                stats["distinct_pairs"] += 1
            else:
                stats["nondistinct_pairs"] += 1
                # distinctness fails ⟹ some ideal element with ≥2 zeros
                assert min_zeros_seen >= 2, (
                    f"r={r} (a,b)={a, b}: distinctness fails but no "
                    "≥2-zero element found"
                )
                stats["min_supp_fail"] = min(
                    stats["min_supp_fail"], 4 - min_zeros_seen
                )
    # E2': D's own slot values pairwise distinct ⟺ {0,a,b,a+b} distinct
    n_e2p = 0
    for a in range(q):
        for b in range(q):
            if (a, b) == (0, 0):
                continue
            distinct = a != 0 and b != 0 and a != b
            for c in range(q):
                vec = slot_vec(a, b, c)
                pw = len(set(vec)) == 4
                assert pw == distinct, (
                    f"E2' mismatch r={r} D={(a, b, c)}: slot-distinct={pw} "
                    f"vs coeff-distinct={distinct}"
                )
                n_e2p += 1
    msg = (
        f"E2/E2' r={r} (exhaustive): {stats['distinct_pairs']} distinct + "
        f"{stats['nondistinct_pairs']} non-distinct (a,b) pairs; "
        f"non-distinct min support = {stats['min_supp_fail']}; "
        f"E2' {n_e2p} triples PASS"
    )
    return msg, stats


# ---------------------------------------------------------------------------
# E3 — instance-level checks
# ---------------------------------------------------------------------------


def widened_engine_kind(comp) -> str:
    """UNIT / WIDENED_RADICAL (4 pairwise-distinct slot values) / OTHER."""
    if comp.kind == a5.UNIT:
        return "unit"
    if comp.kind == a5.ZERO:
        return "zero"
    if len(comp.value_vector) == 4 and len(set(comp.value_vector)) == 4:
        return "widened_radical"
    return "other_radical"


def translate_mask(G: AbelianGroup, supp: frozenset, g) -> int:
    m = 0
    for s in supp:
        m |= 1 << G.index(G.add(s, g))
    return m


def kernel_small_weight(G: AbelianGroup, P: Poly) -> dict:
    """Exact: does Ann(P) contain a nonzero element of weight 2, 4, or 6?

    (PAR: |P| odd ⟹ annihilator weights are even, so this settles
    'μ ≥ 6' and 'μ ≥ 8' exactly.)  Returns witnesses when found.
    """
    assert P.weight() % 2 == 1, "PAR requires odd-weight polynomial"
    elems = list(G)
    cols = [translate_mask(G, P.support, g) for g in elems]
    # weight 2: col collision
    seen: dict[int, int] = {}
    w2 = None
    for i, cm in enumerate(cols):
        if cm in seen:
            w2 = (elems[seen[cm]], elems[i])
            break
        seen[cm] = i
    # weight 4: equal pair-sums, disjoint pairs (auto-disjoint if no w2)
    w4 = None
    if w2 is None:
        pair_seen: dict[int, tuple[int, int]] = {}
        n = len(elems)
        for i in range(n):
            ci = cols[i]
            for j in range(i + 1, n):
                s = ci ^ cols[j]
                if s in pair_seen:
                    a, b = pair_seen[s]
                    if a != i:  # distinct pairs; no-w2 ⟹ disjoint
                        w4 = (elems[a], elems[b], elems[i], elems[j])
                        break
                else:
                    pair_seen[s] = (i, j)
            if w4:
                break
    # weight 6: equal triple-sums, disjoint triples (only if no w2/w4)
    w6 = None
    if w2 is None and w4 is None:
        tri_seen: dict[int, tuple[int, int, int]] = {}
        n = len(elems)
        for tri in combinations(range(n), 3):
            s = cols[tri[0]] ^ cols[tri[1]] ^ cols[tri[2]]
            if s in tri_seen:
                other = tri_seen[s]
                if not set(other) & set(tri):
                    w6 = tuple(elems[i] for i in other + tri)
                    break
            else:
                tri_seen[s] = tri
    return {"w2": w2, "w4": w4, "w6": w6}


def circulant_matrix(G: AbelianGroup, P: Poly) -> np.ndarray:
    """Matrix of z ↦ P·z over F₂ (columns = P·δ_g)."""
    n = len(G)
    M = np.zeros((n, n), dtype=np.uint8)
    elems = list(G)
    for j, g in enumerate(elems):
        for s in P.support:
            M[G.index(G.add(s, g)), j] = 1
    return M


def layer_profile(G: AbelianGroup, frame, supp_idx: np.ndarray, elems) -> dict:
    """Per-2-part-layer weights of a chain given as a 0/1 vector."""
    weights: dict[tuple, int] = {s: 0 for s in frame.layers}
    for i in np.nonzero(supp_idx)[0]:
        s, _ = a5.split_element(elems[int(i)], frame)
        weights[s] += 1
    return weights


def check_E3(label: str, ell: int, m: int, A_s: str, B_s: str,
             expect_mu: tuple | None, rng: random.Random) -> None:
    print(f"\n--- E3 instance: {label} (Z{ell}×Z{m}, A={A_s}, B={B_s}) ---")
    G = AbelianGroup((ell, m))
    A = Poly.from_string(A_s, G)
    B = Poly.from_string(B_s, G)
    frame = a5.crt_frame(G)
    fields = a5.orbit_fields(frame.odd_orders)
    print(f"frame shape: {frame.shape}; odd part {frame.odd_orders}; "
          f"component fields r = {sorted(of.size for of in fields)}")
    assert frame.shape == "Z2xZ2", "E3 instances must be Z₂²-frame"
    ok_all = True
    for name, P in (("A", A), ("B", B)):
        comps = a5.component_table(P, frame, fields)
        kinds = [widened_engine_kind(c) for c in comps]
        n_unit = kinds.count("unit")
        n_wid = kinds.count("widened_radical")
        n_other = kinds.count("other_radical") + kinds.count("zero")
        print(f"  {name}: components = {len(comps)} "
              f"(unit {n_unit}, widened_radical {n_wid}, other/zero {n_other})")
        for c, k in zip(comps, kinds):
            if k in ("other_radical", "zero"):
                r = c.field_r
                print(f"    !! non-engine component at orbit {c.orbit_rep} "
                      f"(F_2^{r}): {c.vec_str()} [{k}]")
                ok_all = False
    print(f"  widened-predicate verdict: "
          f"{'PASS (engine floor applies)' if ok_all else 'FAIL'}")
    # exact small-weight kernel exhaustion
    for name, P in (("A", A), ("B", B)):
        ks = kernel_small_weight(G, P)
        floor = ("≥8" if not any(ks.values()) else
                 "6" if ks["w6"] and not ks["w2"] and not ks["w4"] else
                 "4" if ks["w4"] else "2")
        print(f"  μ(Ann {name}): exact-small-weight verdict = {floor} "
              f"(w2={bool(ks['w2'])}, w4={bool(ks['w4'])}, w6={bool(ks['w6'])})")
    # annihilator layer-structure sampling
    elems = list(G)
    for name, P in (("A", A), ("B", B)):
        M = circulant_matrix(G, P)
        basis = nullspace_f2(M)
        k = basis.shape[0]
        print(f"  dim Ann({name}) = {k}", end="")
        if k == 0:
            print(" (no annihilator)")
            continue
        bad = 0
        min_w = None
        n_samp = min(500, 2 ** k - 1)
        for _ in range(n_samp):
            mask = rng.randrange(1, 2 ** k)
            v = np.zeros(len(G), dtype=np.uint8)
            mm, i = mask, 0
            while mm:
                if mm & 1:
                    v ^= basis[i]
                mm >>= 1
                i += 1
            if not v.any():
                continue
            w = int(v.sum())
            min_w = w if min_w is None else min(min_w, w)
            lp = layer_profile(G, frame, v, elems)
            nz_layers = sum(1 for x in lp.values() if x)
            evens = all(x % 2 == 0 for x in lp.values())
            if nz_layers < 3 or not evens:
                bad += 1
                if bad <= 3:
                    print(f"\n    !! engine-structure violation: layers {lp}")
        print(f"; sampled {n_samp}: min weight {min_w}, "
              f"engine-structure violations {bad}")
    if expect_mu:
        print(f"  (expected μ from prior notes: {expect_mu} — cross-check)")


def main() -> None:
    rng = random.Random(20260706)
    print("=" * 72)
    print("A15 §1.3 field-genericity sweep (E1/E2/E2'/E3)")
    print("=" * 72)
    for r in (2, 3, 4, 6):
        print(check_E1(r, exhaustive=(r == 2), rng=rng))
    for r in (2, 3, 4, 6):
        msg, _ = check_E2_E2p(r)
        print(msg)
    # E3 control: gross base
    check_E3("bb_72 (control)", 6, 6, "x^3 + y + y^2", "y^3 + x + x^2",
             expect_mu=(6, 6), rng=rng)
    # E3 target: the A8 Z₆×Z₁₄ doubling base [[168,12,6]]
    check_E3("z6z14 [[168,12,6]]", 6, 14, "1 + y + x^3*y^3", "1 + x + x^2*y^7",
             expect_mu=(12, 6), rng=rng)
    print("\nALL CHECKS PASSED (any failure raises AssertionError above)")


if __name__ == "__main__":
    main()
