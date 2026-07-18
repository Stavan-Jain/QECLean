"""A15 T1.2 — certifier for the class small-cycle theorem (v1).

Checks the hypotheses of the theorem (A5 goal-2 log, Entry 11.4;
proof = Entries 8–11) for a weight-3 BB instance (Z_ℓ × Z_m, A, B)
and emits a certificate:

    D1   dA, dB multiplicity-free (Sidon; excludes 2-torsion
         differences and periods at weight 3)
    D2   dA ∩ dB = ∅
    iii  mirrored projection pattern (A monomial in exactly one
         axis, B in the other)
    FRM  floor-bearing frame: per-axis 2-part ∈ {1, Z₂} (⟺ 4∤ℓ, 4∤m)
    ANN  Ann(A), Ann(B) ≠ 0 (hypothesis (a) non-vacuity)
    FLR  one-sided floor ≥ 6 — analytic route per frame shape
         (Z₂²: the widened engine predicate, Entry 8.1b; Z₂:
         (1+s)⊗I(W) with 2·d_H(W) ≥ 6, A5 E2; semisimple: I(V)
         with d_H(V) ≥ 6, A5 E4) + the exact weight-2/4 kernel
         exhaustion (with PAR this settles μ ≥ 6 exactly)

    ⟹  no nonzero 1-cycle of weight ≤ 5: d ≥ 6, μ_Z = μ_X ≥ 6, and
        every free-Z₂ cover (same polynomials) has d ≥ 6.

The theorem is UNCONDITIONAL (Entry 13: the P1–P3 polish items are
discharged; write-up of record `A16_class_theorem_writeup.md`).
`--verify` additionally runs the direct (iv)/(v) checks for the
instance (machine confirmation, A_HANDOFF §1 grade).

Usage:
    uv run python scripts/a15_class_certify.py --self-test
    uv run python scripts/a15_class_certify.py --ell 6 --m 14 \
        --A '1 + y + x^3*y^3' --B '1 + x + x^2*y^7' [--verify]
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import sys
from pathlib import Path

LAB_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LAB_ROOT / "src"))

import numpy as np

from bb_lab.group import AbelianGroup
from bb_lab.linalg import nullspace_f2
from bb_lab.poly import Poly

_spec = importlib.util.spec_from_file_location(
    "a15_t11_residue_hunt", LAB_ROOT / "scripts" / "a15_t11_residue_hunt.py"
)
hunt = importlib.util.module_from_spec(_spec)
sys.modules["a15_t11_residue_hunt"] = hunt
_spec.loader.exec_module(hunt)
a5 = sys.modules["a5_instance_hypotheses"]

THEOREM = ("class small-cycle theorem (UNCONDITIONAL; write-up of "
           "record: A16_class_theorem_writeup.md; proof: A5 goal-2 "
           "log Entries 8-13)")


def _widened_kind(comp) -> str:
    if comp.kind == a5.UNIT:
        return "unit"
    if comp.kind == a5.ZERO:
        return "zero"
    if len(comp.value_vector) == 4 and len(set(comp.value_vector)) == 4:
        return "engine_radical_widened"
    return "other"


def _dH(fields, odd_orders, orbit_set, cap=18) -> int | None:
    """min weight of nonzero f ∈ F₂[H] with Fourier support ⊆ orbit_set
    (discovery-grade enumeration, dim-capped)."""
    H = AbelianGroup(odd_orders)
    elems = list(H)
    rows = []
    for of in fields:
        if of.rep in orbit_set:
            continue
        for i in range(of.r):
            rows.append([of.alpha_powers[of.psi_exp(t)][i] for t in elems])
    if not rows:
        return None
    basis = nullspace_f2(np.array(rows, dtype=np.uint8))
    k = basis.shape[0]
    if k == 0 or k > cap:
        return None
    best = None
    for mask in range(1, 2 ** k):
        v = np.zeros(len(elems), dtype=np.uint8)
        mm, i = mask, 0
        while mm:
            if mm & 1:
                v ^= basis[i]
            mm >>= 1
            i += 1
        w = int(v.sum())
        if w and (best is None or w < best):
            best = w
    return best


def certify(ell: int, m: int, A_str: str, B_str: str,
            verify: bool = False, quiet: bool = False) -> dict:
    G = AbelianGroup((ell, m))
    A = Poly.from_string(A_str, G)
    B = Poly.from_string(B_str, G)
    frame = a5.crt_frame(G)
    elems = list(G)
    idx = {g: i for i, g in enumerate(elems)}
    checks: list[tuple[str, bool, str]] = []

    def add(tag, ok, detail):
        checks.append((tag, ok, detail))
        return ok

    # weight + PAR
    wA, wB = len(A.support), len(B.support)
    add("W3", wA == 3 and wB == 3, f"|A|={wA}, |B|={wB} (PAR: odd)")
    if wA == 3 == wB:
        mfA, dA = hunt.diffs(G, A.support)
        mfB, dB = hunt.diffs(G, B.support)
        add("D1", mfA and mfB,
            f"dA mult-free={mfA}, dB mult-free={mfB} "
            "(subsumes: no 2-torsion differences, no periods)")
        coord = tuple(
            not ({d[ax] for d in dA} & {d[ax] for d in dB})
            for ax in range(2))
        add("D2", not (dA & dB),
            f"dA ∩ dB = ∅: {not (dA & dB)} (coord-disjoint {coord})")
        maA = hunt.mono_axes(hunt.proj_supports(G, A.support))
        maB = hunt.mono_axes(hunt.proj_supports(G, B.support))
        add("iii", len(maA) == 1 and len(maB) == 1 and maA != maB,
            f"mono axes: A={maA}, B={maB} (mirrored ⟺ opposite)")
    add("FRM", frame.shape in ("Z2xZ2", "Z2", "semisimple"),
        f"frame {frame.shape} (2-parts {frame.two_orders}; "
        f"floor-bearing ⟺ 4∤ℓ ∧ 4∤m)")

    if all(ok for _, ok, _ in checks):
        fields = a5.orbit_fields(frame.odd_orders)
        route = []
        floor_ok = True
        for name, P in (("A", A), ("B", B)):
            comps = a5.component_table(P, frame, fields)
            kinds = [_widened_kind(c) for c in comps]
            nonunit = [k for k in kinds if k != "unit"]
            add(f"ANN({name})", bool(nonunit),
                f"non-unit components: {len(nonunit)} "
                "(Ann ≠ 0 ⟺ some non-unit)")
            if frame.shape == "Z2xZ2":
                ok = bool(nonunit) and all(
                    k in ("unit", "engine_radical_widened") for k in kinds)
                route.append(
                    f"{name}: widened engine (Entry 8.1b) "
                    f"[{'PASS' if ok else 'FAIL'}]")
                floor_ok &= ok
            elif frame.shape == "Z2":
                W = {c.orbit_rep for c, k in zip(comps, kinds)
                     if k != "unit"}
                zeroes = [c for c, k in zip(comps, kinds) if k == "zero"]
                dh = _dH(fields, frame.odd_orders, W)
                ok = (not zeroes) and dh is not None and 2 * dh >= 6
                route.append(
                    f"{name}: Z₂ engine 2·d_H(W)={2*dh if dh else '?'} "
                    f"(A5 E2) [{'PASS' if ok else 'FAIL/uncapped'}]")
                floor_ok &= ok
            else:
                V = {c.orbit_rep for c, k in zip(comps, kinds)
                     if k == "zero"}
                dh = _dH(fields, frame.odd_orders, V)
                ok = dh is not None and dh >= 6
                route.append(
                    f"{name}: semisimple d_H(V)={dh} (A5 E4) "
                    f"[{'PASS' if ok else 'FAIL/uncapped'}]")
                floor_ok &= ok
            # exact confirmation (always binding): weight-2/4 kernel
            w2, w4 = hunt.small_kernel_flags(G, P.support, elems, idx)
            add(f"FLR({name})", not (w2 or w4),
                f"exact w2/w4 kernel exhaustion: w2={w2}, w4={w4} "
                "(+PAR ⟹ μ ≥ 6)")
        add("FLR-route", floor_ok, "; ".join(route))

    certified = all(ok for _, ok, _ in checks)
    result = {
        "instance": f"Z{ell}xZ{m}, A={A_str}, B={B_str}",
        "checks": [(t, ok, d) for t, ok, d in checks],
        "certified": certified,
    }
    if verify and certified:
        iv_ok, _ = hunt.verdict_iv(G, A, B, dA, dB)
        v_ok = hunt.verdict_v(G, A, B)
        result["verify"] = {"iv": iv_ok, "v": v_ok}
        assert iv_ok and v_ok, "direct (iv)/(v) check failed?!"

    if not quiet:
        print(f"\n─── {result['instance']} ───")
        for t, ok, d in checks:
            print(f"  [{'✓' if ok else '✗'}] {t:10s} {d}")
        if certified:
            print(f"  ⟹ CERTIFIED by the {THEOREM}:")
            print("     no nonzero 1-cycle of weight ≤ 5; d ≥ 6; "
                  "μ_Z = μ_X ≥ 6;")
            print("     every free-Z₂ cover (same polynomials) has "
                  "d ≥ 6 (Theorem-B transfer).")
            if verify:
                print(f"     [--verify: direct (iv)/(v) checks PASS]")
        else:
            first = next(t for t, ok, _ in checks if not ok)
            print(f"  ⟹ REJECTED (first failed gate: {first}) — "
                  "outside the class; no verdict implied.")
    return result


BATTERY = [
    # (label, ell, m, A, B, expect_certified, expected_first_fail)
    ("bb_72 (gross base)", 6, 6, "x^3 + y + y^2", "y^3 + x + x^2",
     True, None),
    ("bb_108", 9, 6, "x^3 + y + y^2", "y^3 + x + x^2", True, None),
    ("bb_90", 15, 3, "x^9 + y + y^2", "1 + x^2 + x^7", True, None),
    ("z6z14 [[168,12,6]]", 6, 14, "1 + y + x^3*y^3", "1 + x + x^2*y^7",
     True, None),
    ("gross-as-base (deep frame)", 12, 6, "x^3 + y + y^2",
     "y^3 + x + x^2", False, "FRM"),
    ("bb_288-base (deep frame)", 12, 12, "x^3 + y^2 + y^7",
     "y^3 + x + x^2", False, "FRM"),
    ("Z3xZ5 falsifier (E6)", 3, 5, "x + y^2 + y^3", "x^2 + y + y^4",
     False, "iii"),
    ("Frobenius square Z7^2", 7, 7, "1 + x^2 + y^2", "1 + x + y",
     False, "iii"),
]


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--ell", type=int)
    ap.add_argument("--m", type=int)
    ap.add_argument("--A", type=str)
    ap.add_argument("--B", type=str)
    ap.add_argument("--verify", action="store_true")
    ap.add_argument("--jsonl", type=Path, default=None)
    args = ap.parse_args()

    if args.self_test:
        out = args.jsonl.open("w") if args.jsonl else None
        n_bad = 0
        for label, ell, m, A_s, B_s, expect, ffail in BATTERY:
            print(f"\n═══ {label} ═══")
            r = certify(ell, m, A_s, B_s, verify=expect)
            if r["certified"] != expect:
                n_bad += 1
                print(f"  !! SELF-TEST MISMATCH: expected "
                      f"certified={expect}")
            elif not expect and ffail:
                first = next(t for t, ok, _ in r["checks"] if not ok)
                if first != ffail:
                    n_bad += 1
                    print(f"  !! expected first fail {ffail}, got {first}")
            if out:
                out.write(json.dumps({"label": label, **r}) + "\n")
        if out:
            out.close()
        print(f"\n{'ALL SELF-TESTS PASS' if n_bad == 0 else f'{n_bad} FAILURES'}")
        sys.exit(0 if n_bad == 0 else 1)

    if None in (args.ell, args.m, args.A, args.B):
        ap.error("--ell/--m/--A/--B required (or --self-test)")
    r = certify(args.ell, args.m, args.A, args.B, verify=args.verify)
    sys.exit(0 if r["certified"] else 2)


if __name__ == "__main__":
    main()
