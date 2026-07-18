"""A10 — the presentation-literal L1-image of a descent screen.

Computes, purely group-theoretically (no SAT), the set of screen rows
(class, epsA, epsB) that are L1-transports of LITERAL axis covers of
presentations equivalent to the stored pair (Aut × swap × translation
orbit), including the full row-level gauge (deck-lift choice and the
Hom(H, Z2) character freedom in the iso onto the cocycle model).

Comparing this image against a screen's verdict rows answers R7's open
question: a rescue row OUTSIDE the image is a *descent-proper* rescue —
a doubling cover that is a literal lift of NO equivalent presentation;
if instead all rescues lie inside the image, the descent screen equals
presentation-closed literal lifting on that base.

    uv run python scripts/a10_l1_image.py
"""

from __future__ import annotations

import glob
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path

LAB_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LAB_ROOT / "src"))
sys.path.insert(0, str(LAB_ROOT / "scripts"))

from bb_lab.group import AbelianGroup
from bb_lab.poly import Poly

from a5_cover_cascade import automorphisms, apply_auto
from a9_lean_target_screen import cover_group
from a10_descent_covers import CoverGroup, monomial_order

BASES = [
    ("toric3", 3, 3, "1 + x", "1 + y"),
    ("toric4", 4, 4, "1 + x", "1 + y"),
    ("hit2", 6, 6, "y^3 + x + x^2", "1 + x*y^5 + x^2*y"),
    ("hit5", 6, 6, "y^3 + x + x^2", "y^5 + x*y + x^2"),
]


def image_rows(ell: int, m: int, A: Poly, B: Poly) -> set:
    H = A.group
    autos = automorphisms(ell, m)
    rows: set = set()

    for axis in ("x", "y"):
        G1 = cover_group(ell, m, axis)
        oc1, oc2 = G1.orders

        def pi1(gc):
            return (gc[0] % ell, gc[1] % m)

        deck1 = (ell % oc1, 0) if axis == "x" else (0, m % oc2)

        for sigma in autos:
            # sigma as a table and its inverse
            tab = {h: apply_auto(Poly(support=frozenset([h]), group=H), sigma, H)
                   for h in H}
            s_of = {h: next(iter(tab[h].support)) for h in H}
            inv = {v: k for k, v in s_of.items()}

            def pi(gc):
                return inv[pi1(gc)]

            # section of pi and its cocycle
            s1 = {}
            for h in H:
                pre = [gc for gc in G1 if pi(gc) == h]
                s1[h] = min(pre)
            def coc1(h, hp):
                return 0 if G1.add(s1[h], s1[hp]) == s1[H.add(h, hp)] else 1

            # Try EVERY cocycle model: (G1, pi) maps into model (c1, c2)
            # iff a trivializing eta of (coc1 - cocc) exists — the eta
            # consistency IS the extension-class test.  On frames with an
            # odd axis several models are equivalent-over-id_H, and the
            # image must include the row in each of them.
            gens = [(1, 0), (0, 1)]
            targets = []  # (Gc, eta) pairs
            for c1 in (0, 1):
                for c2 in (0, 1):
                    Gc = CoverGroup(ell, m, c1, c2)
                    def cocc(h, hp, Gc=Gc):
                        return Gc.add(Gc.sec(h), Gc.sec(hp))[0]
                    for seed1 in (0, 1):
                        for seed2 in (0, 1):
                            seed = {gens[0]: seed1, gens[1]: seed2}
                            eta = {(0, 0): 0}
                            frontier = [(0, 0)]
                            while frontier:
                                h = frontier.pop()
                                for gen in gens:
                                    hp = H.add(h, gen)
                                    if hp in eta:
                                        continue
                                    eta[hp] = (
                                        eta[h] + seed[gen]
                                        + coc1(h, gen) + cocc(h, gen)
                                    ) % 2
                                    frontier.append(hp)
                            if all(
                                (eta[H.add(h, hp)] + eta[h] + eta[hp]) % 2
                                == (coc1(h, hp) + cocc(h, hp)) % 2
                                for h in H for hp in H
                            ):
                                targets.append((Gc, eta))
            if not targets:
                raise RuntimeError("no consistent eta in any model")

            def make_psi(Gc, eta):
                def psi(gc):
                    h = pi(gc)
                    t = 0 if gc == s1[h] else 1
                    out = Gc.sec(h)
                    if (t + eta[h]) % 2:
                        out = Gc.add(out, Gc.deck)
                    return out
                return psi

            for Gc, eta in targets:
                c1, c2 = Gc.c1, Gc.c2
                psi = make_psi(Gc, eta)
                for swapped in (False, True):
                    P, Q = (B, A) if swapped else (A, B)
                    # moved presentation: (sigma(P), sigma(Q)) + g; its literal
                    # axis cover, translated back by a lift of g, via psi
                    sP = apply_auto(P, sigma, H)
                    sQ = apply_auto(Q, sigma, H)
                    for g in H:
                        # cover-side lifts of the base translation g (2 choices)
                        for ghat in [gc for gc in G1 if pi1(gc) == g]:
                            def transport(poly_moved):
                                out = []
                                for s in poly_moved.support:
                                    lit = H.add(g, s)  # literal coords in G1
                                    out.append(psi(G1.sub(lit, ghat)))
                                return frozenset(out)
                            At = transport(sP)
                            Bt = transport(sQ)
                            if swapped:
                                At, Bt = Bt, At
                            if {(a, b) for (s, a, b) in At} != set(A.support):
                                raise RuntimeError("transport error (A)")
                            if {(a, b) for (s, a, b) in Bt} != set(B.support):
                                raise RuntimeError("transport error (B)")
                            def eps_of(supp, Pst):
                                eps = []
                                for mon in monomial_order(Pst):
                                    fib = [gg for gg in supp
                                           if (gg[1], gg[2]) == mon]
                                    assert len(fib) == 1
                                    eps.append(fib[0][0])
                                return tuple(eps)
                            rows.add(((c1, c2), eps_of(At, A), eps_of(Bt, B)))
    return rows


def load_screen(base_id: str) -> dict:
    out = {}
    for f in glob.glob(str(LAB_ROOT / "data" / "a10" / f"{base_id}_descent_screen*.jsonl")):
        for line in open(f):
            if not line.strip():
                continue
            r = json.loads(line)
            out[(tuple(r["cls"]), tuple(r["epsA"]), tuple(r["epsB"]))] = r
    return out


def main() -> None:
    for base_id, ell, m, A_str, B_str in BASES:
        H = AbelianGroup((ell, m))
        A = Poly.from_string(A_str, H)
        B = Poly.from_string(B_str, H)
        img = image_rows(ell, m, A, B)
        per_cls = Counter(cls for cls, _, _ in img)
        n_rows = 4 * 2 ** (len(A.support) + len(B.support))
        print(f"\n### {base_id}: presentation-literal L1-image = "
              f"{len(img)}/{n_rows} rows; per class {dict(per_cls)}")
        screen = load_screen(base_id)
        if not screen:
            continue
        resc_in = resc_out = fail_in = fail_out = other = 0
        outside = []
        img_verdicts = Counter()
        for key, r in screen.items():
            in_img = key in img
            if key in img:
                img_verdicts[r["verdict"]] += 1
            if r["verdict"] in ("rescue", "super"):
                if in_img:
                    resc_in += 1
                else:
                    resc_out += 1
                    outside.append(key)
            elif r["verdict"] == "fail":
                fail_in += in_img
                fail_out += not in_img
            else:
                other += 1
        print(f"  screened {len(screen)}: rescues in-image {resc_in}, "
              f"OUT-OF-IMAGE {resc_out}; fails in/out {fail_in}/{fail_out}; "
              f"other {other}")
        print(f"  image-row verdicts so far: {dict(img_verdicts)}")
        if outside:
            print("  DESCENT-PROPER RESCUES (outside the presentation-literal image):")
            for cls, eA, eB in sorted(outside):
                print(f"    class={cls} epsA={''.join(map(str,eA))} "
                      f"epsB={''.join(map(str,eB))}")


if __name__ == "__main__":
    main()
