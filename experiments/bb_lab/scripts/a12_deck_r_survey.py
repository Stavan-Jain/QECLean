"""A12 Phase A: survey (R) / k-preservation / membership over every
historically-checked free Z2 BB cover.

Rows: gross (x- and y-doubling), the pair72 §5 pair (x-doubling), the
Z6xZ14 [[168,12,6]] base (x- and y-doubling), and all 152 A9 screen pairs
(parsed from notes/A9_lean_target_screen.md).

Per row, computes over F2:
    k_base, k_cover, dim eps*H1(cover), membership 1+s in (A,B),
and checks:
    T1  (theorem):   membership       =>  eps*H1 = 0
    C1  (theorem):   membership      <=>  k_cover = k_base
    INEQ (theorem):  dim eps*H1  >=  k_cover - k_base
    [together these give R*: (R) <=> k preserved <=> membership]
    EQ  (conjecture, Bockstein d^2 = 0):  dim eps*H1 == k_cover - k_base

Run: python3 scripts/a12_deck_r_survey.py     (from experiments/bb_lab)
"""

import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from a12_deck_r_probe import bb_data  # noqa: E402

NOTE = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                    "..", "notes", "A9_lean_target_screen.md")

MONO = re.compile(r"^(?:1|(?:x(?:\^(\d+))?)?(?:\*?y(?:\^(\d+))?)?)$")


def parse_poly(text):
    """'x*y^4 + x^2 + 1' -> [(a, b), ...] exponent pairs."""
    terms = [t.strip() for t in text.split("+")]
    out = []
    for t in terms:
        a = b = 0
        if t == "1":
            out.append((0, 0))
            continue
        for factor in t.split("*"):
            if factor.startswith("x"):
                a = int(factor[2:]) if "^" in factor else 1
            elif factor.startswith("y"):
                b = int(factor[2:]) if "^" in factor else 1
            else:
                raise ValueError(f"bad factor {factor!r} in {text!r}")
        out.append((a, b))
    assert len(out) == 3 or len(out) == 2, f"unexpected weight in {text!r}"
    return out


def swap_xy(poly):
    return [(b, a) for (a, b) in poly]


def survey_row(name, base_l, base_m, A, B, direction):
    """Cover = base with `direction` doubled. Returns the stats tuple."""
    if direction == "y":  # swap coordinates so doubling is always in x
        base_l, base_m = base_m, base_l
        A, B = swap_xy(A), swap_xy(B)
    cover_l = 2 * base_l
    k_cover, dim_eps, member = bb_data(cover_l, base_m, A, B)
    k_base, _, _ = bb_data(base_l, base_m,
                           [(a % base_l, b) for (a, b) in A],
                           [(a % base_l, b) for (a, b) in B])
    jump = k_cover - k_base
    r_holds = dim_eps == 0
    ok_t1 = (not member) or r_holds
    ok_c1 = member == (jump == 0)
    ok_ineq = dim_eps >= jump
    ok_eq = dim_eps == jump
    return (name, k_base, k_cover, dim_eps, member,
            r_holds, ok_t1, ok_c1, ok_ineq, ok_eq)


def a9_rows():
    row_re = re.compile(
        r"^\|\s*(\d+)\s*\|\s*Z(\d+)xZ(\d+)\s*\|\s*([xy])\s*\|[^|]*\|\s*"
        r"`([^`]+)`\s*;\s*`([^`]+)`\s*\|")
    with open(NOTE) as fh:
        for line in fh:
            m = row_re.match(line)
            if m:
                idx, l, mm, d, at, bt = m.groups()
                yield (f"A9#{idx} Z{l}xZ{mm} {d}-dbl",
                       int(l), int(mm), parse_poly(at), parse_poly(bt), d)


def main():
    rows = [
        ("gross Z6xZ6 x-dbl -> Z12xZ6", 6, 6,
         [(3, 0), (0, 1), (0, 2)], [(0, 3), (1, 0), (2, 0)], "x"),
        ("gross Z6xZ6 y-dbl -> Z6xZ12", 6, 6,
         [(3, 0), (0, 1), (0, 2)], [(0, 3), (1, 0), (2, 0)], "y"),
        ("pair72 Z3xZ6 x-dbl -> Z6xZ6", 3, 6,
         [(2, 0), (0, 1), (0, 3)], [(0, 0), (1, 0), (0, 2)], "x"),
        ("z6z14 [[168,12,6]] x-dbl", 6, 14,
         [(0, 0), (0, 1), (3, 3)], [(0, 0), (1, 0), (2, 7)], "x"),
        ("z6z14 [[168,12,6]] y-dbl", 6, 14,
         [(0, 0), (0, 1), (3, 3)], [(0, 0), (1, 0), (2, 7)], "y"),
    ]
    rows.extend(a9_rows())

    n_r, n_member, n_eq, bad = 0, 0, 0, []
    print(f"{'row':38s} {'kb':>3s} {'kc':>3s} {'eH1':>4s} "
          f"{'mem':>3s} {'(R)':>5s} {'EQ':>3s}")
    for spec in rows:
        (name, kb, kc, deps, mem, r_holds,
         ok_t1, ok_c1, ok_ineq, ok_eq) = survey_row(*spec)
        n_r += r_holds
        n_member += bool(mem)
        n_eq += ok_eq
        if not (ok_t1 and ok_c1 and ok_ineq):
            bad.append((name, "THEOREM-VIOLATION"))
        if not ok_eq:
            bad.append((name, f"EQ fails: eps*H1={deps} != jump={kc - kb}"))
        marker = "" if (r_holds and mem and ok_eq) else "   <-- LOOK"
        print(f"{name:38s} {kb:3d} {kc:3d} {deps:4d} "
              f"{'yes' if mem else 'NO':>3s} "
              f"{'HOLD' if r_holds else 'FAIL':>5s} "
              f"{'ok' if ok_eq else 'GAP':>3s}{marker}")

    total = len(rows)
    print(f"\n{total} covers surveyed: (R) holds on {n_r}, "
          f"membership on {n_member}, quantitative EQ on {n_eq}.")
    if bad:
        print("ANOMALIES:")
        for name, why in bad:
            print(f"  {name}: {why}")
        sys.exit(1)
    print("No theorem violations; EQ (Bockstein) conjecture consistent "
          "on all rows.")


if __name__ == "__main__":
    main()
