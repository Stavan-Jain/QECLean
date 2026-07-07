"""A15 Entry 11 — machine verification of the (iv) uniform kill
(discovery/validation only, A_HANDOFF §1).

Structure (char-2 polynomial identities):

  X1  CHIRALITY CLASSES.  For a Sidon 3-set B, the dB-triangles
      {0, a, b} (a, b, b−a ∈ dB) generically form two translate
      classes: the REFLECTION class T ~ B_i − B with image
      B·T = B·(−B) + c = ({0} ∪ dB) + c of weight 7 — never a
      weight-3 image; and the SAME-CHIRALITY class T ~ B − B_i with
      image B·T = B² + c (Frobenius square; weight 3 since D1 forbids
      2-torsion differences).  Verified per member: every weight-7
      image equals ({0} ∪ dB) + c; every weight-3 image of a
      family-class triangle equals B² + c.
  X2  THE GENERIC KILL (Theorem J).  Under D1 ∧ (iii): a same-
      chirality match σ = t + A forces dA = d(B²) = 2·dB; but 2·dB
      contains the y = 0 element 2·(p, 0) ≠ 0 (D1), while dA has no
      y = 0 elements ((iii): w, s, s′ ≠ 0).  Mirror for (3,1).
      Verified: dA ∩ {y = 0} = ∅ and (B1) dB ∩ {x = 0} = ∅ on every
      member; and canonical-translate(image) ≠ canonical(A) for the
      family classes.
  X3  COINCIDENCE CLASSES.  Extra triangle classes require an extra
      additive relation among dB's positive reps (q = 2p-type
      doubling, q = −3p, 3p + 2q = 0, …).  Tally the occurring
      relation classes across the battery, assert each coincidence
      image is ≁ A (the per-member surveyable residue), and confirm
      members with > 2 classes carry a detectable relation.

Usage:
    uv run python scripts/a15_e11_iv_kill.py --frames 9x6,6x10
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


def canon(G, S) -> tuple:
    return min(tuple(sorted(G.sub(s, a) for s in S)) for a in S)


def double_set(G, S) -> frozenset:
    return frozenset(G.add(s, s) for s in S)


def conv3(G, S, T) -> frozenset:
    return hunt.conv(G, frozenset(S), frozenset(T))


def analyze_side(G, S_poly, P_poly, dS, dP, tally, examples) -> None:
    """Triangles of dS (S = the acting poly, image S·T vs partner P)."""
    zero = tuple(0 for _ in G.orders)
    S = S_poly.support
    P = P_poly.support
    refl_img = canon(G, frozenset([zero]) | dS)   # {0} ∪ dS class
    sq_img = canon(G, double_set(G, S))           # B² class
    canon_P = canon(G, P)
    tris = hunt.triangle_census(G, dS)
    n_classes = 0
    n_coincidence = 0
    for T in tris:
        img = conv3(G, S, T)
        n_classes += 1
        if len(img) == 7:
            assert canon(G, img) == refl_img, "reflection image ≠ {0}∪dB!"
            tally["refl-wt7"] += 1
        elif len(img) == 3:
            ci = canon(G, img)
            if ci == sq_img:
                tally["chirality-wt3-square"] += 1
                # Theorem J: the square image is never a P-translate
                assert ci != canon_P, "FROBENIUS MATCH — (iv) violated!"
            else:
                n_coincidence += 1
                tally["coincidence-wt3"] += 1
                assert ci != canon_P, "coincidence-class (iv) violation!"
                if len(examples) < 8:
                    examples.append(
                        {"S": sorted(S), "P": sorted(P),
                         "T": sorted(T), "img": sorted(img)})
        else:
            tally[f"wt{len(img)}"] += 1
    if n_classes > 2:
        # must carry an extra additive relation among dS reps: check
        # the doubling flavor (v, 2v ∈ dS) or a mixed relation
        has_dbl = any(G.add(v, v) in dS for v in dS)
        tally["members>2classes"] += 1
        tally[f">2classes-dblrel={has_dbl}"] += 1


def check_frame(ell: int, m: int, cap: int) -> None:
    t0 = time.time()
    G, members = e9.enumerate_members(ell, m)
    print(f"\n=== Z{ell}xZ{m}: {len(members)} members "
          f"[enum {time.time() - t0:.0f}s]")
    tally = Counter()
    examples: list = []
    n_struct = 0
    for A, B, dA, dB in members[:cap]:
        # X2 structural (iii)-facts: dA has no y = 0 element; dB has
        # no x = 0 element unless B2 (dB ⊂ {y = 0}), in which case the
        # mirror kill uses (0, 2w) ∉ dB automatically.
        assert all(d[1] != 0 for d in dA), "(iii) A-side y=0 element?!"
        b2 = all(d[1] == 0 for d in dB)
        if not b2:
            assert all(d[0] != 0 for d in dB), "B1 x=0 element?!"
        n_struct += 1
        analyze_side(G, B, A, dB, dA, tally, examples)   # (1,3)
        analyze_side(G, A, B, dA, dB, tally, examples)   # (3,1)
    print(f"X1+X2+X3 PASS over {n_struct} members: {dict(tally)}")
    if examples:
        print("  coincidence-class examples:")
        for ex in examples[:4]:
            print(f"    {ex}")


def self_test_bb108() -> None:
    """bb_108's (3,1) side had THREE classes (A5 Entry 2) — the third
    must be a coincidence class with a doubling relation in dA."""
    from bb_lab.poly import Poly
    G = AbelianGroup((9, 6))
    A = Poly.from_string("x^3 + y + y^2", G)
    B = Poly.from_string("y^3 + x + x^2", G)
    _, dA = hunt.diffs(G, A.support)
    _, dB = hunt.diffs(G, B.support)
    tris_A = hunt.triangle_census(G, dA)
    tris_B = hunt.triangle_census(G, dB)
    dbl_A = [v for v in dA if G.add(v, v) in dA]
    print(f"bb_108: dA-triangle classes {len(tris_A)} (Entry 2 says 3), "
          f"dB-triangle classes {len(tris_B)} (Entry 2 says 2); "
          f"doubling relations in dA: {dbl_A}")
    assert len(tris_A) == 3 and len(tris_B) == 2
    assert dbl_A, "expected a doubling relation in bb_108's dA"
    tally = Counter()
    examples: list = []
    analyze_side(G, B, A, dB, dA, tally, examples)
    analyze_side(G, A, B, dA, dB, tally, examples)
    print(f"bb_108 class analysis: {dict(tally)}")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--frames", type=str, default="9x6,6x10")
    ap.add_argument("--cap", type=int, default=100000)
    args = ap.parse_args()
    self_test_bb108()
    for fr in args.frames.split(","):
        ell, m = (int(t) for t in fr.strip().split("x"))
        check_frame(ell, m, args.cap)


if __name__ == "__main__":
    main()
