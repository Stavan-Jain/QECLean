"""A15 T1.1 — falsify-first hunt for the (C-iv′)/(C-v′) residue lemma.

Fresh even-axis mirror frames (where the corrected weight lemma's
2δ ≡ 0 orbit-pair branch — A5 E7.3 — is LIVE, unlike every frame the
Entry-6 sweeps covered): enumerate weight-3 translation-classes of
(A, B) with the class hypotheses

    (b)   dA, dB multiplicity-free and dA ∩ dB = ∅
    (iii) mirrored projection pattern (A monomial in one axis, B in the
          other; both full weight-3 on their non-monomial axis)
    (a)   Ann(A), Ann(B) ≠ 0 and exact μ(Ann) ≥ 6 (PAR kills odd
          weights; weight-2/4 kernel exhaustion is exact, so the gate
          is exact — no engine reasoning is load-bearing here)

and check (iv)/(v) directly.  Any violation falsifies (C-iv′)/(C-v′).
On clean frames, tally the E6.4 kill pipeline over the (2,2) table:

    stage 1  y-projection weight test — branch: zero-gap / 3-AP /
             orbit-pair (the fresh even-axis branch) / weight-kill
    stage 2  x-projection mirror
    stage 3  the residue: exact translate comparison; record which
             multiplicity profile (x / y / neither) separates the sets

Stage-3 rows with tag "neither" are configurations the multiplicity-
profile lemma CANNOT kill as stated — the exact data the T1 lemma
drafting needs.  Discovery/validation only (A_HANDOFF §1).

Usage:
    uv run python scripts/a15_t11_residue_hunt.py --frames 9x6
    uv run python scripts/a15_t11_residue_hunt.py \
        --frames 9x6,6x10,15x6 --jsonl data/a15/t11_hunt.jsonl
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import sys
import time
from collections import Counter
from pathlib import Path

LAB_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LAB_ROOT / "src"))

import numpy as np

from bb_lab.group import AbelianGroup
from bb_lab.poly import Poly

_spec = importlib.util.spec_from_file_location(
    "a5_instance_hypotheses", LAB_ROOT / "scripts" / "a5_instance_hypotheses.py"
)
a5 = importlib.util.module_from_spec(_spec)
sys.modules["a5_instance_hypotheses"] = a5
_spec.loader.exec_module(a5)


# ---------------------------------------------------------------------------
# (iv)/(v) verdicts — same logic as a5_class_census_sweep.py (copied to
# avoid that script's duckdb import; keep in sync)
# ---------------------------------------------------------------------------


def conv(G: AbelianGroup, p: frozenset, q: frozenset) -> frozenset:
    counts: dict[tuple[int, ...], int] = {}
    for a in p:
        for b in q:
            c = G.add(a, b)
            counts[c] = counts.get(c, 0) + 1
    return frozenset(c for c, k in counts.items() if k % 2)


def triangle_census(G: AbelianGroup, dS: frozenset) -> list[frozenset]:
    classes: set[frozenset] = set()
    for a in dS:
        for b in dS:
            if a == b:
                continue
            if G.sub(b, a) in dS:
                tri = frozenset([tuple(0 for _ in G.orders), a, b])
                cands = [frozenset(G.sub(t, mn) for t in tri) for mn in tri]
                classes.add(min(cands, key=lambda s: sorted(s)))
    return sorted(classes, key=lambda s: sorted(s))


def verdict_iv(G, A, B, dA, dB) -> tuple[bool, list]:
    """(iv) + per-triangle records for the kill-profile stats."""
    elems = list(G)
    ok = True
    records = []
    for (S, P, tag) in ((B, A, "13"), (A, B, "31")):
        dS = dB if tag == "13" else dA
        for tri in triangle_census(G, dS):
            img = conv(G, S.support, tri)
            if len(img) != 3:
                continue
            matched = any(
                frozenset(G.add(a, t) for a in P.support) == img
                for t in elems
            )
            if matched:
                ok = False
            records.append({
                "split": tag, "triangle": sorted(tri),
                "image": sorted(img), "matched": matched,
                "kill": None if matched else _profile_tag(
                    img, frozenset(P.support), G),
            })
    return ok, records


def verdict_v(G, A, B) -> bool:
    elems = list(G)
    zero = tuple(0 for _ in G.orders)
    nonzero = [g for g in elems if g != zero]
    right: dict[int, set[frozenset]] = {}
    for dr in nonzero:
        base = conv(G, B.support, frozenset([zero, dr]))
        for t in elems:
            img = frozenset(G.add(c, t) for c in base)
            right.setdefault(len(img), set()).add(img)
    for dl in nonzero:
        sigL = conv(G, A.support, frozenset([zero, dl]))
        if sigL and sigL in right.get(len(sigL), set()):
            return False
    return True


# ---------------------------------------------------------------------------
# gates
# ---------------------------------------------------------------------------


def diffs(G, supp) -> tuple[bool, frozenset]:
    lst = [G.sub(a, b) for a in supp for b in supp if a != b]
    return len(lst) == len(set(lst)), frozenset(lst)


def proj_supports(G, supp) -> tuple[frozenset, ...]:
    out = []
    for ax in range(G.rank):
        counts: dict[int, int] = {}
        for g in supp:
            counts[g[ax]] = counts.get(g[ax], 0) + 1
        out.append(frozenset(x for x, c in counts.items() if c % 2))
    return tuple(out)


def mono_axes(projs) -> list[int]:
    return [i for i, s in enumerate(projs) if len(s) == 1]


def translate_mask(G, supp, g, idx) -> int:
    m = 0
    for s in supp:
        m |= 1 << idx[G.add(s, g)]
    return m


def small_kernel_flags(G, supp, elems, idx) -> tuple[bool, bool]:
    """(has weight-2 annihilator, has weight-4 annihilator) — exact."""
    cols = [translate_mask(G, supp, g, idx) for g in elems]
    seen: dict[int, int] = {}
    for i, cm in enumerate(cols):
        if cm in seen:
            return True, False
        seen[cm] = i
    pair_seen: set[int] = set()
    n = len(elems)
    for i in range(n):
        ci = cols[i]
        for j in range(i + 1, n):
            s = ci ^ cols[j]
            if s in pair_seen:
                return False, True  # no w2 ⟹ collision pairs disjoint
            pair_seen.add(s)
    return False, False


def has_nonunit_component(P, frame, fields) -> bool:
    return any(
        c.kind != a5.UNIT for c in a5.component_table(P, frame, fields)
    )


def gf2_rank(M: np.ndarray) -> int:
    M = M.copy() % 2
    r = 0
    rows, cols = M.shape
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if M[i, c]:
                piv = i
                break
        if piv is None:
            continue
        M[[r, piv]] = M[[piv, r]]
        for i in range(rows):
            if i != r and M[i, c]:
                M[i] ^= M[r]
        r += 1
        if r == rows:
            break
    return r


def gf2_solvable(Mcols: list[int], b: int, nbits: int) -> bool:
    """Does Σ x_j · col_j = b have a solution over F₂? (columns as ints)"""
    basis: list[int] = []  # row-echelon over bit positions
    pivots: list[int] = []
    for col in Mcols:
        cur = col
        for p, bs in zip(pivots, basis):
            if (cur >> p) & 1:
                cur ^= bs
        if cur:
            p = cur.bit_length() - 1
            basis.append(cur)
            pivots.append(p)
    cur = b
    for p, bs in zip(pivots, basis):
        if (cur >> p) & 1:
            cur ^= bs
    return cur == 0


# ---------------------------------------------------------------------------
# the (2,2) pipeline classifier (E6.4, mirrored orientation:
# A monomial in x, B monomial in y)
# ---------------------------------------------------------------------------


def _weight_1d(supp1d: frozenset, d: int, m: int) -> int:
    """|s(y)·(1+y^d)| in F₂[Z_m] for s a set of exponents."""
    counts: dict[int, int] = {}
    for p in supp1d:
        for q in (p, (p + d) % m):
            counts[q] = counts.get(q, 0) + 1
    return sum(1 for c in counts.values() if c % 2)


def _is_3ap(supp1d: frozenset, d: int, m: int) -> bool:
    return any(supp1d == frozenset(((p) % m, (p + d) % m, (p + 2 * d) % m))
               for p in supp1d)


def _is_orbit_pair(supp1d: frozenset, d: int, m: int) -> bool:
    return (2 * d) % m == 0 and any((p + d) % m in supp1d for p in supp1d)


def _profile_tag(S1: frozenset, S2: frozenset, G) -> str:
    """Which coordinate multiplicity profile separates S1 from S2
    (translation-invariant)?  'x' / 'y' / 'both' / 'neither'."""
    def prof(S, ax):
        c: dict[int, int] = {}
        for g in S:
            c[g[ax]] = c.get(g[ax], 0) + 1
        return tuple(sorted(c.values()))
    dx = prof(S1, 0) != prof(S2, 0)
    dy = prof(S1, 1) != prof(S2, 1)
    return {(True, True): "both", (True, False): "x",
            (False, True): "y", (False, False): "neither"}[(dx, dy)]


def classify_22(G, A, B, dA, dB) -> dict:
    """Run the E6.4 pipeline over all (δL, δR); return tallies + the
    stage-3 residue rows (with profile tags) + any exact matches."""
    ell, m = G.orders
    zero = (0, 0)
    ay = frozenset(g[1] for g in A.support)   # full 3-set (A mono-x)
    bx = frozenset(g[0] for g in B.support)   # full 3-set (B mono-y)
    tally = Counter()
    residue_rows = []
    matches = []
    nonzero = [g for g in G if g != zero]
    # canonical forms of right images for exact stage-3 comparison
    for dl in nonzero:
        sigL = conv(G, A.support, frozenset([zero, dl]))
        wL = len(sigL)
        # stage 1: y-projection.  π_y(σL) = a(y)(1+y^{dl_y}) weight;
        # RHS π_y = y^β(1+y^{dr_y}) weight ∈ {0, 2}.
        wLy = _weight_1d(ay, dl[1], m)
        # stage 2 precompute: π_x(σL) = x^α(1+x^{dl_x}) weight ∈ {0,2}
        wLx = 0 if dl[0] == 0 else 2
        if dl[1] == 0:
            br1 = "y-zero-gap"
        elif wLy == 2:
            br1 = ("y-3AP" if _is_3ap(ay, dl[1], m) else
                   "y-orbit-pair" if _is_orbit_pair(ay, dl[1], m) else
                   "y-w2-other")
        else:
            br1 = None  # LHS y-weight ∉ {0,2}: no δR can match
        for dr in nonzero:
            key = None
            # stage 1 test
            rhs_y = 0 if dr[1] == 0 else 2
            if wLy != rhs_y:
                key = "s1-y-weight"
            else:
                # stage 2 test (mirror): π_x(σR) = b(x)(1+x^{dr_x})
                wRx = _weight_1d(bx, dr[0], ell)
                if wLx != wRx:
                    key = "s2-x-weight"
            if key is None:
                # stage 3: the residue — exact translate comparison
                sigR = conv(G, B.support, frozenset([zero, dr]))
                if len(sigR) != wL:
                    key = "s3-size"
                else:
                    matched = any(
                        frozenset(G.add(c, t) for c in sigR) == sigL
                        for t in G
                    )
                    if matched:
                        matches.append({"dl": dl, "dr": dr,
                                        "sigma": sorted(sigL)})
                        key = "MATCH"
                    else:
                        tag = _profile_tag(sigL, sigR, G)
                        br2 = ("x-3AP" if _is_3ap(bx, dr[0], ell) else
                               "x-orbit-pair" if _is_orbit_pair(bx, dr[0], ell)
                               else "x-zero-gap" if dr[0] == 0 else
                               "x-w2-other")
                        row = {
                            "dl": dl, "dr": dr, "size": wL,
                            "branch_y": br1, "branch_x": br2,
                            "profile_kill": tag,
                        }
                        key = f"s3-residue-{tag}"
                        if tag == "neither":
                            # the finer invariants (A15 T1.1 probe):
                            # difference multiset + the D1∧D2 incidence
                            # criterion (size-6 only; necessary condition)
                            dmL = Counter(G.sub(p, q) for p in sigL
                                          for q in sigL if p != q)
                            dmR = Counter(G.sub(p, q) for p in sigR
                                          for q in sigR if p != q)
                            row["dm_separates"] = dmL != dmR
                            if wL == 6:
                                incA = all(
                                    (G.add(d, dr) in dB or G.add(d, dr) == zero)
                                    and (G.sub(d, dr) in dB
                                         or G.sub(d, dr) == zero)
                                    for d in dA)
                                incB = all(
                                    (G.add(e, dl) in dA or G.add(e, dl) == zero)
                                    and (G.sub(e, dl) in dA
                                         or G.sub(e, dl) == zero)
                                    for e in dB)
                                row["incidence_kills"] = not (incA and incB)
                            if not row["dm_separates"]:
                                key = "s3-residue-DM-RESISTANT"
                        residue_rows.append(row)
            tally[key] += 1
    return {"tally": tally, "residue": residue_rows, "matches": matches}


# ---------------------------------------------------------------------------
# the hunt
# ---------------------------------------------------------------------------


def hunt_frame(ell: int, m: int, classify_cap: int, jsonl,
               member_cap: int) -> dict:
    t0 = time.time()
    G = AbelianGroup((ell, m))
    frame = a5.crt_frame(G)
    fields = a5.orbit_fields(frame.odd_orders)
    elems = list(G)
    idx = {g: i for i, g in enumerate(elems)}
    zero = (0, 0)
    print(f"\n{'=' * 72}\nframe Z{ell}×Z{m}  (|G|={len(elems)}, "
          f"frame shape {frame.shape}, even axes "
          f"{[i for i, o in enumerate((ell, m)) if o % 2 == 0]})")

    # per-poly enumeration + cheap gates
    cands = []
    nz = [g for g in elems if g != zero]
    for i in range(len(nz)):
        for j in range(i + 1, len(nz)):
            supp = frozenset([zero, nz[i], nz[j]])
            mf, dS = diffs(G, supp)
            if not mf:
                continue
            projs = proj_supports(G, supp)
            ma = mono_axes(projs)
            if len(ma) != 1:
                continue
            cands.append((supp, dS, ma[0]))
    n_mirror = len(cands)
    # expensive per-poly gates, only for mirror candidates
    polys = []
    for supp, dS, ax in cands:
        P = Poly.from_support(supp, G)
        if not has_nonunit_component(P, frame, fields):
            continue  # Ann = 0: vacuous member, excluded (E6.1)
        w2, w4 = small_kernel_flags(G, supp, elems, idx)
        if w2 or w4:
            continue  # exact floor < 6
        polys.append((P, dS, ax))
    bx = [(P, dS) for P, dS, ax in polys if ax == 0]  # monomial in x
    by = [(P, dS) for P, dS, ax in polys if ax == 1]  # monomial in y
    print(f"weight-3 translation-classes: {len(nz) * (len(nz) - 1) // 2}; "
          f"mult-free+mirrored: {n_mirror}; +floor/Ann gates: "
          f"{len(polys)} (mono-x {len(bx)}, mono-y {len(by)})")

    # pairs (A mono-x, B mono-y; the swapped orientation is the same
    # code family under the x↔y relabeling)
    members = []
    for A, dA in bx:
        for B, dB in by:
            if dA & dB:
                continue
            members.append((A, B, dA, dB))
    print(f"members (b: disjoint diff sets): {len(members)}")
    if len(members) > member_cap:
        print(f"  !! member cap {member_cap} hit — checking the first "
              f"{member_cap} (deterministic order)")
        members = members[:member_cap]

    # (iv)/(v) + pipeline
    stats = {"frame": f"Z{ell}xZ{m}", "members": len(members),
             "iv_fail": 0, "v_fail": 0, "violations": []}
    agg_tally = Counter()
    agg_iv_kills = Counter()
    neither_examples = []
    n_classified = 0
    for n_done, (A, B, dA, dB) in enumerate(members):
        iv_ok, iv_records = verdict_iv(G, A, B, dA, dB)
        v_ok = verdict_v(G, A, B)
        for rec in iv_records:
            if not rec["matched"]:
                agg_iv_kills[(rec["split"], rec["kill"])] += 1
        if not (iv_ok and v_ok):
            # follow-up: exhibit + stabilizer/logical classification
            viol = {"frame": f"Z{ell}xZ{m}",
                    "A": sorted(A.support), "B": sorted(B.support),
                    "iv_ok": iv_ok, "v_ok": v_ok}
            cls = classify_22(G, A, B, dA, dB)
            if cls["matches"]:
                mt = cls["matches"][0]
                # cycle u = ({0,δL}, translate of {0,δR}); stabilizer?
                dl, dr = mt["dl"], mt["dr"]
                sigL = conv(G, A.support, frozenset([zero, dl]))
                # find t with match
                for t in G:
                    sigR = conv(G, B.support, frozenset([zero, dr]))
                    if frozenset(G.add(c, t) for c in sigR) == sigL:
                        break
                uL = [zero, dl]
                uR = [t, G.add(t, dr)]
                # u ∈ im ∂₂ = {(B w, A w)}?  columns (B δ_g, A δ_g)
                cols = []
                nbits = 2 * len(elems)
                for g in elems:
                    cm = 0
                    for s in B.support:
                        cm |= 1 << idx[G.add(s, g)]
                    for s in A.support:
                        cm |= 1 << (len(elems) + idx[G.add(s, g)])
                    cols.append(cm)
                b = 0
                for u in uL:
                    b |= 1 << idx[u]
                for u in uR:
                    b |= 1 << (len(elems) + idx[u])
                stab = gf2_solvable(cols, b, nbits)
                viol["witness"] = {"dl": dl, "dr": dr, "t": t,
                                   "in_im_d2": stab}
            stats["violations"].append(viol)
            stats["iv_fail"] += 0 if iv_ok else 1
            stats["v_fail"] += 0 if v_ok else 1
            print(f"  !!! VIOLATION at member {n_done}: {viol}")
        if n_classified < classify_cap:
            cls = classify_22(G, A, B, dA, dB)
            agg_tally.update(cls["tally"])
            n_classified += 1
            for row in cls["residue"]:
                if row["profile_kill"] == "neither":
                    if len(neither_examples) < 12:
                        neither_examples.append(
                            {"A": sorted(A.support), "B": sorted(B.support),
                             **{k: row[k] for k in
                                ("dl", "dr", "size", "branch_y", "branch_x")}}
                        )
            if cls["matches"] and v_ok:
                print("  !! classifier/verdict_v disagreement — bug")
        if jsonl:
            jsonl.write(json.dumps({
                "frame": f"Z{ell}xZ{m}", "A": sorted(A.support),
                "B": sorted(B.support), "iv": iv_ok, "v": v_ok,
            }) + "\n")
        if (n_done + 1) % 500 == 0:
            print(f"  ... {n_done + 1}/{len(members)} members "
                  f"({time.time() - t0:.0f}s)")

    print(f"\n(iv) fails: {stats['iv_fail']}   (v) fails: {stats['v_fail']}"
          f"   [{time.time() - t0:.0f}s]")
    print(f"(2,2) pipeline tally over {n_classified} classified members:")
    for k, c in sorted(agg_tally.items(), key=lambda kv: -kv[1]):
        print(f"    {k:24s} {c}")
    n_res = sum(c for k, c in agg_tally.items() if k.startswith("s3-residue"))
    n_nei = agg_tally.get("s3-residue-neither", 0)
    print(f"  stage-3 residue rows: {n_res}; profile-lemma-resistant "
          f"('neither'): {n_nei}")
    if neither_examples:
        print("  'neither' examples (first few):")
        for ex in neither_examples[:6]:
            print(f"    {ex}")
    print("  (iv) kill-profile tags:", dict(agg_iv_kills))
    stats["tally"] = {k: int(v) for k, v in agg_tally.items()}
    stats["n_classified"] = n_classified
    stats["neither_examples"] = neither_examples
    return stats


def self_test() -> None:
    """bb_108's stored presentation must pass everything (A5 Entry 2)."""
    G = AbelianGroup((9, 6))
    A = Poly.from_string("x^3 + y + y^2", G)
    B = Poly.from_string("y^3 + x + x^2", G)
    mfA, dA = diffs(G, A.support)
    mfB, dB = diffs(G, B.support)
    assert mfA and mfB and not (dA & dB)
    assert mono_axes(proj_supports(G, A.support)) == [0]
    assert mono_axes(proj_supports(G, B.support)) == [1]
    elems = list(G)
    idx = {g: i for i, g in enumerate(elems)}
    assert small_kernel_flags(G, A.support, elems, idx) == (False, False)
    assert small_kernel_flags(G, B.support, elems, idx) == (False, False)
    iv_ok, _ = verdict_iv(G, A, B, dA, dB)
    assert iv_ok and verdict_v(G, A, B), "bb_108 must pass (iv)+(v)"
    print("self-test (bb_108 gates + iv/v): PASS")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--frames", type=str, default="9x6")
    ap.add_argument("--classify-cap", type=int, default=200,
                    help="max members per frame to run the full (2,2) "
                    "pipeline classification on")
    ap.add_argument("--member-cap", type=int, default=20000)
    ap.add_argument("--jsonl", type=Path, default=None)
    args = ap.parse_args()

    self_test()
    out = None
    if args.jsonl:
        args.jsonl.parent.mkdir(parents=True, exist_ok=True)
        out = args.jsonl.open("w")
    all_stats = []
    for fr in args.frames.split(","):
        ell, m = (int(t) for t in fr.strip().split("x"))
        all_stats.append(
            hunt_frame(ell, m, args.classify_cap, out, args.member_cap))
    if out:
        out.close()
    print(f"\n{'=' * 72}\nSUMMARY")
    total_viol = 0
    for st in all_stats:
        total_viol += len(st["violations"])
        print(f"  {st['frame']}: members {st['members']}, "
              f"iv_fail {st['iv_fail']}, v_fail {st['v_fail']}, "
              f"neither-rows "
              f"{st['tally'].get('s3-residue-neither', 0)}"
              f"/{st['n_classified']} classified")
    print("VERDICT:",
          "COUNTEREXAMPLE(S) FOUND — (C-iv′)/(C-v′) falsified, see above"
          if total_viol else
          "no violations — conjecture survives these frames")


if __name__ == "__main__":
    main()
