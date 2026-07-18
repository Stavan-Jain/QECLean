"""A15 Entry 10 — machine verification of the two remaining (v)-crumbs
(discovery/validation only, A_HANDOFF §1; each check mirrors a proof
step of Entry 10).

Size-4 (δ := δ_L ∈ dA, δ′ := δ_R ∈ dB):

  W1  Lemma E (exact rigidity): Σ-count formulas over dA per row, and
      the joint rigidity (M′ ≡ dA ∧ M ≡ dB as multisets) never holds
      on gate-passing members.
  W2  Matching dichotomy (Lemma F): a match aligns σ_L's pair
      decomposition (gaps {δ, 2δ}) with σ_R's ({δ′, 2δ′}) inside one
      4-set, so one of:
        aligned      {δ} = {±δ′}            — D2-impossible (count 0)
        crossed      δ = ±2δ′ ∧ 2δ = ∓δ′    — forces 3δ′ = 0 (then
                     δ = ∓δ′: D2-impossible, count 0) or 5δ′ = 0
                     (PENTAGONAL — count; dies by W4)
        M₂-branch    {±e, ±(e+δ)} = {±δ′, ±2δ′} — forces e or e+δ
                     ∈ dB: D2-impossible (count 0)
        M₃-branch    {±(δ−e), ±(e+2δ)} = {±δ′, ±2δ′} — TRIANGULAR
                     residual (count + sub-relation stats)
  W4  Pentagonal census over Z₅² (the confinement lemma reduces the
      5-torsion branch to a FIXED Z₅×Z₅ table): enumerate all
      difference-set data (δ, e | δ′, f) with D1 ∧ D2, and count
      σ-shape translate matches — both shape-free and restricted to
      the crossed relations.  Expect 0 ⟹ branch universally dead.

S2 (Entry 9 branch 2b; δ_L ∈ dB, δ_R ∈ dA, sizes 6):

  W3  The D2-funnel: an S2 match forces [a(y) is an AP with
      difference ±w (the dA pair-gap)] ∧ [h = ±2w, or 3u = 0 ∧
      h = ±w] — which places a dB slant (±u, ±w-family) inside dA,
      contradicting D2.  Machine form: no gate-passing S2-hard row
      satisfies the forced-condition set (count 0); b-side orbit-pair
      S2-hard rows (killed by the ≤4 < 6 count) and a-side orbit-pair
      rows (killed by 4 ∤ m) are counted separately (expect 0).

Usage:
    uv run python scripts/a15_e10_size4_s2_kills.py --frames 9x6,6x10
"""

from __future__ import annotations

import argparse
import importlib.util
import sys
import time
from collections import Counter
from pathlib import Path

LAB_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LAB_ROOT / "src"))

_spec = importlib.util.spec_from_file_location(
    "a15_e9", LAB_ROOT / "scripts" / "a15_e9_residue_lemma_checks.py"
)
e9 = importlib.util.module_from_spec(_spec)
sys.modules["a15_e9"] = e9
_spec.loader.exec_module(e9)
hunt = sys.modules["a15_t11_residue_hunt"]

from bb_lab.group import AbelianGroup  # noqa: E402


def size4_data(G, A, dl):
    """(a_i, a_j, a_k, e) for δ := dl ∈ dA (Sidon-unique)."""
    pair = [(p, q) for p in A.support for q in A.support
            if p != q and G.sub(p, q) == dl]
    ai, aj = pair[0]
    ak = next(iter(A.support - {ai, aj}))
    return ai, aj, ak, G.sub(aj, ak)


def pm(G, *vals) -> Counter:
    c: Counter = Counter()
    for v in vals:
        c[v] += 1
        c[G.neg(v)] += 1
    return c


# ---------------------------------------------------------------------------
# W1 + W2 over all size-4 rows of the sampled members
# ---------------------------------------------------------------------------


def check_W12(G, members, cap) -> str:
    zero = tuple(0 for _ in G.orders)
    tally = Counter()
    tri_rows = []
    for A, B, dA, dB in members[:cap]:
        dA_ms = Counter()
        for d in dA:
            dA_ms[d] += 1
        for dl in dA:
            _, _, _, e = size4_data(G, A, dl)
            two_dl = G.add(dl, dl)
            M = pm(G, two_dl, G.sub(e, dl), G.add(e, two_dl))
            for dr in dB:
                tally["rows"] += 1
                _, _, _, f = size4_data(G, B, dr)
                two_dr = G.add(dr, dr)
                Mp = pm(G, two_dr, G.sub(f, dr), G.add(f, two_dr))
                # W1: Σ-count formula over dA
                sL = e9.sigma(G, A.support, dl)
                dmL = e9.dmultiset(G, sL)
                lhs = sum(dmL[d] for d in dA)
                pred = 6 + sum(cnt for v, cnt in M.items() if v in dA)
                assert lhs == pred, "W1 Σ-formula fail"
                # W1: joint rigidity never holds
                dB_ms = Counter()
                for x in dB:
                    dB_ms[x] += 1
                if Mp == dA_ms and M == dB_ms:
                    tally["JOINT-RIGIDITY"] += 1
                    print(f"  !! W1 joint rigidity holds: "
                          f"A={sorted(A.support)} B={sorted(B.support)}")
                # W2 branch preconditions
                gapsL = pm(G, dl, two_dl)
                gapsR = pm(G, dr, two_dr)
                if gapsL == gapsR:
                    # aligned (δ = ±δ′) is D2-impossible; crossed:
                    if dl == dr or dl == G.neg(dr):
                        tally["W2-ALIGNED-D2-VIOLATION"] += 1
                    else:
                        three = G.add(dr, two_dr)
                        five = G.add(three, two_dr)
                        if three == zero:
                            tally["W2-CROSSED-3TORSION"] += 1
                        elif five == zero:
                            tally["W2-crossed-pentagonal"] += 1
                        else:
                            tally["W2-crossed-other"] += 1
                if pm(G, e, G.add(e, dl)) == gapsR:
                    tally["W2-M2-D2-VIOLATION"] += 1
                if pm(G, G.sub(dl, e), G.add(e, two_dl)) == gapsR:
                    tally["W2-M3-triangular"] += 1
                    tri_rows.append((A, B, dl, dr, e, f))
    # the D2-violation and 3-torsion counters must be 0 on gate-passing
    # members (their preconditions contradict D2)
    for k in ("W2-ALIGNED-D2-VIOLATION", "W2-M2-D2-VIOLATION",
              "W2-CROSSED-3TORSION", "JOINT-RIGIDITY"):
        assert tally[k] == 0, f"{k} = {tally[k]} — derivation hole!"
    msg = f"W1+W2 PASS: {dict(tally)}"
    if tri_rows:
        msg += f"\n  triangular rows (M3 precondition): {len(tri_rows)}"
        for A, B, dl, dr, e, f in tri_rows[:4]:
            msg += (f"\n    A={sorted(A.support)} B={sorted(B.support)} "
                    f"dl={dl} dr={dr}")
    return msg


# ---------------------------------------------------------------------------
# W3 — the S2 funnel
# ---------------------------------------------------------------------------


def a_shape(G, A):
    """(iii)-A1 structure: (u, pair_gap_w, spike, pair) or None (A2)."""
    from collections import defaultdict
    byx = defaultdict(list)
    for g in A.support:
        byx[g[0]].append(g)
    xs = [x for x, lst in byx.items() if len(lst) == 2]
    if not xs:
        return None  # A2 (all same x) or not A1-shaped
    px = xs[0]
    pair = byx[px]
    spike = next(g for g in A.support if g[0] != px)
    u = (spike[0] - px) % G.orders[0]
    w = (pair[0][1] - pair[1][1]) % G.orders[1]
    return u, w, spike, pair


def check_W3(G, members, cap) -> str:
    ell, m = G.orders
    _, tally, s2_rows = e9.check_V2(G, members, cap)
    pinned = []
    branch = Counter()
    for A, B, dA, dB, dl, dr in s2_rows:
        ay = frozenset(g[1] for g in A.support)
        bx = frozenset(g[0] for g in B.support)
        if dl[1] == 0 or dr[0] == 0:
            continue
        if e9.w1d(ay, dl[1], m) != 2 or e9.w1d(bx, dr[0], ell) != 2:
            continue
        a_ap = hunt._is_3ap(ay, dl[1], m)
        b_ap = hunt._is_3ap(bx, dr[0], ell)
        branch[("a", "AP" if a_ap else "orbitpair")] += 1
        branch[("b", "AP" if b_ap else "orbitpair")] += 1
        pinned.append((A, B, dl, dr, a_ap, b_ap))
    n_funnel = 0
    for A, B, dl, dr, a_ap, b_ap in pinned:
        sh = a_shape(G, A)
        if sh is None:
            continue
        u, w, spike, pair = sh
        ay = frozenset(g[1] for g in A.support)
        # h: dB slant y-gap (B1: spike-y − pair-y)
        from collections import defaultdict
        byy = defaultdict(list)
        for g in B.support:
            byy[g[1]].append(g)
        ys = [y for y, lst in byy.items() if len(lst) == 2]
        if not ys:
            continue  # B2
        h = (next(g for g in B.support if g[1] != ys[0])[1] - ys[0]) % m
        cond_ap = hunt._is_3ap(ay, w, m)  # a(y) is an AP w/ diff ±w
        cond_h = (h == (2 * w) % m or h == (-2 * w) % m
                  or ((3 * u) % ell == 0
                      and (h == w or h == (-w) % m)))
        if cond_ap and cond_h:
            n_funnel += 1
            print(f"  !! W3 funnel conditions co-hold (D2 hole?): "
                  f"A={sorted(A.support)} B={sorted(B.support)}")
    assert n_funnel == 0, "W3 funnel violated"
    assert branch[("b", "orbitpair")] == 0, "b-side orbit-pair S2-hard!"
    assert branch[("a", "orbitpair")] == 0, "a-side orbit-pair S2-hard!"
    return (f"W3 PASS: S2 {len(s2_rows)} → pinned {len(pinned)} "
            f"(branches {dict(branch)}), funnel-condition rows 0")


# ---------------------------------------------------------------------------
# W4b — the μ₅/Ann kill: EVERY weight-3 poly on Z₅² has all components
# unit (no vanishing weight-3 sums of 5th roots of unity in char 2), so
# any pentagonal-confined A has Ann(A) = 0 and hypothesis (a) fails.
# ---------------------------------------------------------------------------


def check_W4b() -> str:
    from bb_lab.poly import Poly
    a5 = sys.modules["a5_instance_hypotheses"]
    G = AbelianGroup((5, 5))
    frame = a5.crt_frame(G)
    fields = a5.orbit_fields(frame.odd_orders)
    zero = (0, 0)
    nz = [g for g in G if g != zero]
    n_polys = 0
    for i in range(len(nz)):
        for j in range(i + 1, len(nz)):
            P = Poly.from_support(frozenset([zero, nz[i], nz[j]]), G)
            comps = a5.component_table(P, frame, fields)
            assert all(c.kind == a5.UNIT for c in comps), (
                f"non-unit component on Z₅² at {sorted(P.support)}"
            )
            n_polys += 1
    return (f"W4b PASS: all {n_polys} weight-3 polys on Z₅² have "
            "all-unit components (Ann = 0 — the pentagonal branch "
            "violates hypothesis (a))")


# ---------------------------------------------------------------------------
# W5 — confined-data census: the M₃/closure equations force any size-4
# match's data into small-torsion rank-≤2 subgroups (T3-counting, T9
# dup, 5δ = 0 / 15-torsion cyclic, Z₅² pentagonal).  Exhaustive census
# of σ-shape translate matches with D1 ∧ D2 over the covering ambient
# groups: cyclic Z_n (n ≤ 60) and Z_n × Z₃ (n ≤ 30).
# ---------------------------------------------------------------------------


def _census(G) -> tuple[int, int]:
    zero = tuple(0 for _ in G.orders)
    nz = [g for g in G if g != zero]

    def canon(S):
        return min(tuple(sorted(G.sub(s, a) for s in S)) for a in S)

    by_shape: dict = {}
    for d in nz:
        if G.add(d, d) == zero:
            continue  # 2-torsion δ violates D1
        for e in nz:
            vals = [d, G.neg(d), e, G.neg(e), G.add(e, d),
                    G.neg(G.add(e, d))]
            if len(set(vals)) != 6:
                continue
            if any(G.add(v, v) == zero for v in vals):
                continue  # 2-torsion difference violates D1
            ds = frozenset(vals)
            shape = frozenset([zero, G.neg(e), G.add(d, d), G.sub(d, e)])
            if len(shape) != 4:
                continue
            by_shape.setdefault(canon(shape), []).append((d, e, ds))
    n_d2 = n_all = 0
    for lst in by_shape.values():
        for (d1, e1, dsA) in lst:
            for (d2, e2, dsB) in lst:
                if (d1, e1) == (d2, e2):
                    continue
                n_all += 1
                if not (dsA & dsB):
                    n_d2 += 1
    return n_all, n_d2


def check_W5() -> str:
    lines = []
    total_d2 = 0
    for n in range(3, 61):
        n_all, n_d2 = _census(AbelianGroup((n,)))
        total_d2 += n_d2
        if n_d2:
            lines.append(f"  Z_{n}: {n_d2} D1∧D2 σ-shape matches")
    for n in range(3, 31):
        n_all, n_d2 = _census(AbelianGroup((n, 3)))
        total_d2 += n_d2
        if n_d2:
            lines.append(f"  Z_{n}×Z₃: {n_d2} D1∧D2 matches")
    verdict = (f"W5: {total_d2} confined D1∧D2 σ-shape matches across "
               "the family ambients (5|n only — the pentagonal/15-"
               "torsion families; each must die by (iii)∧(a): W5b)")
    return verdict + ("\n" + "\n".join(lines) if lines else "")


def check_W5b() -> str:
    """Realize EVERY 2-D-ambient census hit and assert it fails the
    class gates jointly: never [(iii)-mirrored ∧ Ann(A),Ann(B) ≠ 0 ∧
    no weight-2/4 kernel] — the (iii)∧(a) kill, exhaustively."""
    from bb_lab.poly import Poly
    a5 = sys.modules["a5_instance_hypotheses"]
    ambients = ([(n, 3) for n in range(3, 31)]
                + [(n, 5) for n in range(3, 21)] + [(5, 5)])
    n_hits = n_gate_pass = 0
    import numpy as np
    for orders in ambients:
        G = AbelianGroup(orders)
        elems = list(G)
        idx = {g: i for i, g in enumerate(elems)}
        n = len(elems)

        def ann_nonzero(supp) -> bool:
            M = np.zeros((n, n), dtype=np.uint8)
            for j, g in enumerate(elems):
                for s in supp:
                    M[idx[G.add(s, g)], j] = 1
            return hunt.gf2_rank(M) < n
        zero = tuple(0 for _ in orders)
        nz = [g for g in elems if g != zero]

        def canon(S):
            return min(tuple(sorted(G.sub(s, a) for s in S)) for a in S)

        by_shape: dict = {}
        for d in nz:
            if G.add(d, d) == zero:
                continue
            for e in nz:
                vals = [d, G.neg(d), e, G.neg(e), G.add(e, d),
                        G.neg(G.add(e, d))]
                if len(set(vals)) != 6:
                    continue
                if any(G.add(v, v) == zero for v in vals):
                    continue
                shape = frozenset([zero, G.neg(e), G.add(d, d),
                                   G.sub(d, e)])
                if len(shape) != 4:
                    continue
                by_shape.setdefault(canon(shape), []).append(
                    (d, e, frozenset(vals)))
        gate_cache: dict = {}

        def gates(d, e):
            key = (d, e)
            if key not in gate_cache:
                A = Poly.from_support([zero, d, G.neg(e)], G)
                ma = hunt.mono_axes(hunt.proj_supports(G, A.support))
                ann = ann_nonzero(A.support)
                w2, w4 = hunt.small_kernel_flags(G, A.support, elems, idx)
                gate_cache[key] = (ma, ann, not (w2 or w4))
            return gate_cache[key]

        for lst in by_shape.values():
            for (d1, e1, dsA) in lst:
                for (d2, e2, dsB) in lst:
                    if (d1, e1) == (d2, e2) or (dsA & dsB):
                        continue
                    n_hits += 1
                    maA, annA, flA = gates(d1, e1)
                    maB, annB, flB = gates(d2, e2)
                    mirrored = (len(maA) == 1 and len(maB) == 1
                                and maA[0] != maB[0])
                    if mirrored and annA and annB and flA and flB:
                        n_gate_pass += 1
                        print(f"  !! W5b GATE-PASSING confined match on "
                              f"Z{orders}: A0 d,e={d1},{e1} "
                              f"B0 d,e={d2},{e2}")
    assert n_gate_pass == 0, "confined match passes the class gates!"
    return (f"W5b PASS: {n_hits} realized confined matches across the "
            "2-D family ambients; 0 satisfy (iii)-mirrored ∧ Ann ≠ 0 ∧ "
            "floor — the (iii)∧(a) kill is exhaustive on the census")


# ---------------------------------------------------------------------------
# W4 — the pentagonal census over Z₅²
# ---------------------------------------------------------------------------


def check_W4() -> str:
    G = AbelianGroup((5, 5))
    zero = (0, 0)
    nz = [g for g in G if g != zero]

    def dset(d, e):
        vals = [d, G.neg(d), e, G.neg(e), G.add(e, d), G.neg(G.add(e, d))]
        return frozenset(vals) if len(set(vals)) == 6 else None

    def canon(S):
        return min(tuple(sorted(G.sub(s, a) for s in S)) for a in S)

    cands = []
    for d in nz:
        for e in nz:
            if e == d or e == G.neg(d):
                continue
            ds = dset(d, e)
            if ds is None:
                continue
            shape = frozenset([zero, G.neg(e), G.add(d, d),
                               G.sub(d, e)])
            cands.append((d, e, ds, canon(shape)))
    by_shape = {}
    for d, e, ds, cs in cands:
        by_shape.setdefault(cs, []).append((d, e, ds))
    n_match_pairs = n_pent = 0
    for cs, lst in by_shape.items():
        for dl, e, dsA in lst:
            for dr, f, dsB in lst:
                if dsA & dsB:
                    continue  # D2
                n_match_pairs += 1
                two_dr = G.add(dr, dr)
                if dl == two_dr or dl == G.neg(two_dr):
                    n_pent += 1
    return (f"W4 (Z₅² census): {len(cands)} (δ,e) data, "
            f"σ-shape-matching D2-disjoint pairs = {n_match_pairs} "
            f"(pentagonal-relation subset {n_pent}) — "
            + ("PASS (0: branch universally dead)" if n_match_pairs == 0
               else "!! NONZERO — pentagonal branch live, see rows"))


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--frames", type=str, default="9x6,6x10")
    ap.add_argument("--cap", type=int, default=1200)
    args = ap.parse_args()
    print(check_W4())
    print(check_W4b())
    print(check_W5())
    print(check_W5b())
    for fr in args.frames.split(","):
        ell, m = (int(t) for t in fr.strip().split("x"))
        t0 = time.time()
        G, members = e9.enumerate_members(ell, m)
        print(f"\n=== Z{ell}xZ{m}: {len(members)} members "
              f"[enum {time.time() - t0:.0f}s]")
        print(check_W12(G, members, args.cap))
        print(check_W3(G, members, min(args.cap, 800)))


if __name__ == "__main__":
    main()
