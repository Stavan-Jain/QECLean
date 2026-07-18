"""A15 Entry 9 — machine verification of the (C-res) residue-lemma
derivation, step by step (discovery/validation only, A_HANDOFF §1;
every check mirrors a named proof step so a failure localizes the
derivation error).

Size-6 rows (δ_L ∉ dA, δ_R ∉ dB), match σ_L = t + σ_R:

  V1  multiset formula:
      d(σ_L) = 2·dA ⊎ (dA+δ_L) ⊎ (dA−δ_L) ⊎ {δ_L}³ ⊎ {−δ_L}³
      (and the size-4 analogue below) — formula vs direct computation.
  V2  ATOM STEP: match ⟹ [δ_L = ±δ_R] ∨ [δ_L ∈ dB], and mirror
      [δ_R = ±δ_L] ∨ [δ_R ∈ dA]:
      mult_{d(σ_L)}(δ_L) = 3 + [2δ_L ∈ dA] ≥ 3, while
      mult_{d(σ_R)}(δ_L) ≤ 2 when δ_L ∉ dB ∧ δ_L ≠ ±δ_R.
      Branch tally over ALL size-6 rows:
        DEAD-BY-ATOMS | 2a (δ_L = ±δ_R) | S2 (δ_L ∈ dB ∧ δ_R ∈ dA).
  V3  2a RIGIDITY: for δ := δ_L = ±δ_R, match ⟹ dB = dA + δ = dA − δ
      (Σ-count over dA).  Verified corpus-wide as: no member has dB a
      translate of dA at all (canonical translate classes differ) —
      the 2a branch is dead on every member.
  V4  PROFILE-SHAPE LEMMA: for 3-subsets of Z_ℓ, the ±difference
      6-multiset has shape (3 distinct values, multiplicities 2,2,2)
      ⟺ 4 | ℓ (needs an order-4 element); shape (1 value × 6) never.
      This is what makes dB = dA + δ impossible under (iii) on
      floor-bearing frames.
  V5  S2 PINNING: rows with δ_L ∈ dB ∧ δ_R ∈ dA ∧ δ_L ≠ ±δ_R must
      further satisfy (projection weight lemma, both axes):
      δ_Ry ≠ 0 and δ_Lx ≠ 0 (automatic from the shapes), δ_Ly ≠ 0,
      |a(y)·(1+y^{δ_Ly})| = 2 and |b(x)·(1+x^{δ_Rx})| = 2.
      Tally how many S2 rows survive the pinning ("S2-hard"), and for
      those verify the difference multisets still separate (dm kill).
  V6  size-4 (δ_L ∈ dA ∧ δ_R ∈ dB): formula
      d(σ_L) = ±{δ, 2δ, e, e−δ, e+δ, e+2δ}  (δ := δ_L; e := a_j−a_k
      for the Sidon-unique pair a_i − a_j = δ, third element a_k);
      dm comparison over ALL size-4 rows; tally of the coupled
      necessary system dB = {±2δ, ±(e−δ), ±(e+2δ)} (expect 0).

Usage:
    uv run python scripts/a15_e9_residue_lemma_checks.py \
        --frames 9x6 [--v2-cap 44064] [--jsonl-members data/a15/...jsonl]
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

from bb_lab.group import AbelianGroup
from bb_lab.poly import Poly

_spec = importlib.util.spec_from_file_location(
    "a15_t11_residue_hunt", LAB_ROOT / "scripts" / "a15_t11_residue_hunt.py"
)
hunt = importlib.util.module_from_spec(_spec)
sys.modules["a15_t11_residue_hunt"] = hunt
_spec.loader.exec_module(hunt)
a5 = sys.modules["a5_instance_hypotheses"]


def dmultiset(G, S) -> Counter:
    return Counter(G.sub(p, q) for p in S for q in S if p != q)


def sigma(G, S, delta) -> frozenset:
    zero = tuple(0 for _ in G.orders)
    return hunt.conv(G, S, frozenset([zero, delta]))


# ---------------------------------------------------------------------------
# member enumeration (same gates as the hunt)
# ---------------------------------------------------------------------------


def enumerate_members(ell: int, m: int):
    G = AbelianGroup((ell, m))
    frame = a5.crt_frame(G)
    fields = a5.orbit_fields(frame.odd_orders)
    elems = list(G)
    idx = {g: i for i, g in enumerate(elems)}
    zero = (0, 0)
    nz = [g for g in elems if g != zero]
    polys = []
    for i in range(len(nz)):
        for j in range(i + 1, len(nz)):
            supp = frozenset([zero, nz[i], nz[j]])
            mf, dS = hunt.diffs(G, supp)
            if not mf:
                continue
            ma = hunt.mono_axes(hunt.proj_supports(G, supp))
            if len(ma) != 1:
                continue
            P = Poly.from_support(supp, G)
            if not hunt.has_nonunit_component(P, frame, fields):
                continue
            w2, w4 = hunt.small_kernel_flags(G, supp, elems, idx)
            if w2 or w4:
                continue
            polys.append((P, dS, ma[0]))
    bx = [(P, d) for P, d, ax in polys if ax == 0]
    by = [(P, d) for P, d, ax in polys if ax == 1]
    return G, [(A, B, dA, dB) for A, dA in bx for B, dB in by
               if not (dA & dB)]


# ---------------------------------------------------------------------------
# V1 — multiset formulas
# ---------------------------------------------------------------------------


def check_V1(G, members, n_members=25) -> str:
    zero = tuple(0 for _ in G.orders)
    nz = [g for g in G if g != zero]
    n6 = n4 = 0
    for A, B, dA, dB in members[:n_members]:
        for dl in nz:
            sL = sigma(G, A.support, dl)
            direct = dmultiset(G, sL)
            if dl not in dA:                      # size 6
                pred = Counter()
                for d in dA:
                    pred[d] += 2
                    pred[G.add(d, dl)] += 1
                    pred[G.sub(d, dl)] += 1
                pred[dl] += 3
                pred[G.neg(dl)] += 3
                assert pred == direct, f"V1 size-6 fail A={sorted(A.support)} dl={dl}"
                n6 += 1
            else:                                 # size 4
                # Sidon-unique ordered pair a_i − a_j = dl; third a_k
                pair = [(p, q) for p in A.support for q in A.support
                        if p != q and G.sub(p, q) == dl]
                assert len(pair) == 1, "Sidon violation?"
                ai, aj = pair[0]
                ak = next(iter(A.support - {ai, aj}))
                e = G.sub(aj, ak)
                pred = Counter()
                for v in (dl, G.add(dl, dl), e, G.sub(e, dl),
                          G.add(e, dl), G.add(e, G.add(dl, dl))):
                    pred[v] += 1
                    pred[G.neg(v)] += 1
                assert pred == direct, f"V1 size-4 fail A={sorted(A.support)} dl={dl}"
                n4 += 1
    return f"V1 PASS: {n6} size-6 + {n4} size-4 formula checks"


# ---------------------------------------------------------------------------
# V2 — atom step + branch tally over all size-6 rows
# ---------------------------------------------------------------------------


def multR_at(G, dB, dr, v) -> int:
    """mult of value v in d(σ_R) via the size-6 formula."""
    m = 2 * (v in dB)
    m += (G.sub(v, dr) in dB) + (G.add(v, dr) in dB)
    if v == dr:
        m += 3
    if v == G.neg(dr):
        m += 3
    return m


def check_V2(G, members, cap, validate_n=2000) -> tuple[str, Counter, list]:
    zero = tuple(0 for _ in G.orders)
    nz = [g for g in G if g != zero]
    tally = Counter()
    s2_rows = []
    n_validated = 0
    for A, B, dA, dB in members[:cap]:
        for dl in nz:
            if dl in dA:
                continue
            two_dl = G.add(dl, dl)
            # mult_{d(σL)}(δL) = 3 + [2δL ∈ dA] + 3·[2δL = 0]  (the ±δL
            # atoms coincide at 2-torsion δL), always ≥ 3
            mL = 3 + (two_dl in dA) + 3 * (two_dl == zero)
            for dr in nz:
                if dr in dB:
                    continue
                mR = multR_at(G, dB, dr, dl)
                if dl == dr or dl == G.neg(dr):
                    tally["2a"] += 1
                elif dl in dB and dr in dA:
                    tally["S2"] += 1
                    s2_rows.append((A, B, dA, dB, dl, dr))
                else:
                    # DEAD BY ATOMS: assert the mult mismatch
                    if dl not in dB:
                        assert mR <= 2 < mL, "atom-L bound violated"
                        tally["dead-atom-L"] += 1
                    else:  # mirror atom at δR must kill (δR ∉ dA here)
                        two_dr = G.add(dr, dr)
                        mR2 = 3 + (two_dr in dB) + 3 * (two_dr == zero)
                        mL2 = multR_at(G, dA, dl, dr)
                        assert mL2 <= 2 < mR2, "atom-R bound violated"
                        tally["dead-atom-R"] += 1
                    if n_validated < validate_n:
                        # confirm formula against the real multisets
                        sL = sigma(G, A.support, dl)
                        sR = sigma(G, B.support, dr)
                        assert dmultiset(G, sL)[dl] == mL
                        assert dmultiset(G, sR)[dl] == mR
                        n_validated += 1
    return (f"V2 PASS: branch tally {dict(tally)} "
            f"({n_validated} formula-validated)"), tally, s2_rows


# ---------------------------------------------------------------------------
# V3 — 2a rigidity: dB is never a translate of dA (corpus-wide)
# ---------------------------------------------------------------------------


def canon_class(G, S: frozenset) -> tuple:
    return min(
        (tuple(sorted(G.sub(s, anchor) for s in S)) for anchor in S)
    )


def check_V3(G, members) -> str:
    n_translate = 0
    for A, B, dA, dB in members:
        if canon_class(G, dA) == canon_class(G, dB):
            n_translate += 1
            print(f"  !! V3: dB IS a translate of dA: "
                  f"A={sorted(A.support)} B={sorted(B.support)}")
    return (f"V3 {'PASS' if n_translate == 0 else 'ALERT'}: "
            f"{n_translate}/{len(members)} members with dB ∈ "
            f"translate-class(dA) — 2a branch dead member-wide"
            if n_translate == 0 else f"V3 ALERT: {n_translate} members")


# ---------------------------------------------------------------------------
# V4 — the profile-shape lemma over Z_ℓ
# ---------------------------------------------------------------------------


def check_V4(l_range=range(3, 25)) -> str:
    """The SHIFT LEMMA exactly as the 2a kill uses it: for 4 ∤ ℓ, the
    x-difference multiset of a 3-subset of Z_ℓ (= {±p, ±q, ±(p+q)},
    all nonzero) is NEVER a shift of an A-shape x-profile — either
    {0², u², (−u)²} (u ≠ 0; degenerates to {0², u⁴} at 2u = 0) or
    {0⁶} (shape A2).  At 4 | ℓ exceptions exist (order-4 APs) — the
    frame hypothesis is load-bearing."""
    lines = []
    ok = True
    for ell in l_range:
        # all dB-side multisets from anchored triples {0, c2, c3}
        b_multisets = set()
        for c2 in range(1, ell):
            for c3 in range(c2 + 1, ell):
                diffs = []
                for a, b in ((0, c2), (0, c3), (c2, c3)):
                    d = (a - b) % ell
                    diffs += [d, (-d) % ell]
                b_multisets.add(tuple(sorted(diffs)))
        # all A-shape profiles + all shifts
        hits = 0
        for u in range(1, ell):
            base = sorted([0, 0, u, u, (-u) % ell, (-u) % ell])
            for s in range(ell):
                shifted = tuple(sorted((v + s) % ell for v in base))
                if shifted in b_multisets:
                    hits += 1
        base6 = [0] * 6
        for s in range(ell):
            if tuple(sorted((v + s) % ell for v in base6)) in b_multisets:
                hits += 1
        has4 = ell % 4 == 0
        if (hits > 0) != has4:
            ok = False
            lines.append(f"  !! V4 fail at ℓ={ell}: shift-hits {hits}, "
                         f"4|ℓ={has4}")
        elif hits:
            lines.append(f"  V4 info: ℓ={ell} (4|ℓ): {hits} (u, shift) "
                         "coincidences (order-4 APs, as predicted)")
    return ("V4 PASS (shift lemma): dB-x-multiset is a shift of an "
            "A-shape x-profile ⟺ 4 | ℓ\n" + "\n".join(lines)) if ok \
        else "V4 FAIL\n" + "\n".join(lines)


# ---------------------------------------------------------------------------
# V5 — S2 pinning + dm kill on S2-hard rows
# ---------------------------------------------------------------------------


def w1d(supp1d, d, mod) -> int:
    c: Counter = Counter()
    for p in supp1d:
        c[p % mod] += 1
        c[(p + d) % mod] += 1
    return sum(1 for v in c.values() if v % 2)


def check_V5(G, s2_rows) -> str:
    ell, m = G.orders
    pinned = []
    for A, B, dA, dB, dl, dr in s2_rows:
        ay = frozenset(g[1] for g in A.support)
        bx = frozenset(g[0] for g in B.support)
        # pinning predicates (each a proven projection-weight necessity)
        if dl[1] == 0:            # δ_Ly = 0 ⟹ |π_y σL| = 0 vs |π_y σR| = 2
            continue
        if dr[0] == 0:
            continue
        if w1d(ay, dl[1], m) != 2:
            continue
        if w1d(bx, dr[0], ell) != 2:
            continue
        pinned.append((A, B, dl, dr))
    n_dm_equal = 0
    examples = []
    for A, B, dl, dr in pinned:
        sL = sigma(G, A.support, dl)
        sR = sigma(G, B.support, dr)
        if dmultiset(G, sL) == dmultiset(G, sR):
            n_dm_equal += 1
            examples.append((sorted(A.support), sorted(B.support), dl, dr))
    msg = (f"V5: S2 rows {len(s2_rows)}, surviving projection pinning "
           f"(S2-hard) {len(pinned)}, of which DM-EQUAL {n_dm_equal}")
    if examples:
        msg += "\n  !! DM-resistant S2 rows (need finer invariant):"
        for ex in examples[:6]:
            msg += f"\n    {ex}"
    return msg


# ---------------------------------------------------------------------------
# V6 — size-4: formula (in V1) + dm kill + coupled-system tally
# ---------------------------------------------------------------------------


def check_V6(G, members, cap) -> str:
    n_rows = n_dm_equal = n_coupled = 0
    examples = []
    for A, B, dA, dB in members[:cap]:
        for dl in dA:
            pair = [(p, q) for p in A.support for q in A.support
                    if p != q and G.sub(p, q) == dl]
            ai, aj = pair[0]
            ak = next(iter(A.support - {ai, aj}))
            e = G.sub(aj, ak)
            two_dl = G.add(dl, dl)
            target = set()
            for v in (two_dl, G.sub(e, dl), G.add(e, two_dl)):
                target.add(v)
                target.add(G.neg(v))
            for dr in dB:
                n_rows += 1
                if frozenset(target) == dB:
                    n_coupled += 1
                sL = sigma(G, A.support, dl)
                sR = sigma(G, B.support, dr)
                if dmultiset(G, sL) == dmultiset(G, sR):
                    n_dm_equal += 1
                    if len(examples) < 6:
                        examples.append(
                            (sorted(A.support), sorted(B.support), dl, dr))
    msg = (f"V6: size-4 rows {n_rows}, DM-EQUAL {n_dm_equal}, "
           f"coupled-system holds {n_coupled}")
    if examples:
        msg += "\n  !! size-4 DM-resistant rows:"
        for ex in examples:
            msg += f"\n    {ex}"
    return msg


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--frames", type=str, default="9x6")
    ap.add_argument("--v2-cap", type=int, default=1200,
                    help="members for the V2 all-rows branch tally")
    ap.add_argument("--v6-cap", type=int, default=4000)
    args = ap.parse_args()

    print(check_V4())
    for fr in args.frames.split(","):
        ell, m = (int(t) for t in fr.strip().split("x"))
        t0 = time.time()
        G, members = enumerate_members(ell, m)
        print(f"\n=== frame Z{ell}xZ{m}: {len(members)} members "
              f"[enum {time.time() - t0:.0f}s]")
        print(check_V1(G, members))
        msg, tally, s2_rows = check_V2(G, members, args.v2_cap)
        print(msg)
        print(check_V3(G, members))
        print(check_V5(G, s2_rows))
        print(check_V6(G, members, args.v6_cap))


if __name__ == "__main__":
    main()
