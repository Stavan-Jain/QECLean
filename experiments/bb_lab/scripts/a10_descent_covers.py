"""A10 — group-structured free-Z2 descent covers of BB codes.

The descent space of a base presentation `(H = Z_ell x Z_m, A, B)`
(A10 plan §2): four cocycle extension classes `(c1, c2) ∈ Z2²` times
`2^(w_A + w_B)` sheet-assignment twists.  Every cover is modeled
uniformly on the set `Z2 × Z_ell × Z_m` with carry-cocycle addition

    (s,a,b) + (s',a',b') = (s + s' + c1·[a+a' ≥ ell] + c2·[b+b' ≥ m],
                            a+a' mod ell,  b+b' mod m)

so `proj(s,a,b) = (a,b)`, `deck = (1,0,0)`, `sec(a,b) = (0,a,b)` — the
`XDoubleCoverData` field list verbatim.  Class (1,0) is the x-axis
cover (iso to Z_{2ell} × Z_m via `(s,a,b) ↦ (a + ell·s, b)`), (0,1)
the y-axis cover, (1,1) the mixed class (new when both axes even),
(0,0) the split class (zero twist = two disjoint base copies).

A twist `(epsA, epsB)` lifts the i-th monomial (in sorted-support
order) of A resp. B to sheet `epsA[i]` resp. `epsB[i]`.  Weight is
preserved and `fiberSum(cover poly) = base poly` holds by construction
(distinct base monomials have disjoint fibers).

Distance side: for ANY BB-form code `H_X = [M_A | M_B]`,
`H_Z = [M_Bᵀ | M_Aᵀ]` over any finite abelian group — twisted covers
included — `d_X = d_Z` via the inversion duality: `M_Pᵀ = M_{ι(P)}`
with `ι(P)(g) = P(−g)` a ring automorphism of F₂[G], and
`v = (v_L, v_R) ↦ (ι(v_R), ι(v_L))` maps X-logicals bijectively onto
Z-logicals, weight-preserving (the A3 Entry-13 argument, group-
agnostic).  The screen therefore computes `d_X` only; the test suite
spot-checks the identity numerically.

Screen driver (fail-fast, JSONL-resumable):

    uv run python scripts/a10_descent_covers.py screen \
        --ell 6 --m 6 --A "y^3 + x + x^2" --B "y^5 + x*y + x^2" \
        --base-id hit5 --d-base 6 --k-base 12 \
        --out data/a10/hit5_descent_screen.jsonl

    uv run python scripts/a10_descent_covers.py toric --L 3
"""

from __future__ import annotations

import argparse
import itertools
import json
import sys
import time
from dataclasses import dataclass
from pathlib import Path

import numpy as np

LAB_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LAB_ROOT / "src"))

from bb_lab.checks import CheckMatrices, assert_css_commutation, bb_check_matrices
from bb_lab.group import AbelianGroup
from bb_lab.linalg import rank_f2
from bb_lab.poly import Poly
from bb_lab.sat_distance import _solve_at_weight, find_logical_z


# ---------------------------------------------------------------------------
# The cover group (uniform cocycle model)
# ---------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class CoverGroup:
    """Z2-extension of Z_ell × Z_m with cocycle class (c1, c2), on the
    set Z2 × Z_ell × Z_m.  Duck-types the `AbelianGroup` surface that
    `Poly`/`circulant`/`bb_check_matrices` consume (`cardinality`,
    iteration in index order, `sub`, `reduce`, `orders`)."""

    ell: int
    m: int
    c1: int
    c2: int

    @property
    def orders(self) -> tuple[int, int, int]:
        # Coordinate ranges of the (s, a, b) representation — NOT the
        # abstract invariant factors (class (1,0) is iso to Z_2ell × Z_m).
        return (2, self.ell, self.m)

    @property
    def rank(self) -> int:
        return 3

    @property
    def cardinality(self) -> int:
        return 2 * self.ell * self.m

    def __len__(self) -> int:
        return self.cardinality

    def __iter__(self):
        for s in range(2):
            for a in range(self.ell):
                for b in range(self.m):
                    yield (s, a, b)

    def index(self, g: tuple[int, int, int]) -> int:
        s, a, b = self.reduce(g)
        return (s * self.ell + a) * self.m + b

    def from_index(self, i: int) -> tuple[int, int, int]:
        b = i % self.m
        i //= self.m
        a = i % self.ell
        s = i // self.ell
        return (s, a, b)

    def reduce(self, g: tuple[int, int, int]) -> tuple[int, int, int]:
        s, a, b = g
        return (s % 2, a % self.ell, b % self.m)

    def add(self, g: tuple[int, int, int], h: tuple[int, int, int]) -> tuple[int, int, int]:
        s1, a1, b1 = self.reduce(g)
        s2, a2, b2 = self.reduce(h)
        carry_x = 1 if a1 + a2 >= self.ell else 0
        carry_y = 1 if b1 + b2 >= self.m else 0
        return (
            (s1 + s2 + self.c1 * carry_x + self.c2 * carry_y) % 2,
            (a1 + a2) % self.ell,
            (b1 + b2) % self.m,
        )

    def neg(self, g: tuple[int, int, int]) -> tuple[int, int, int]:
        s, a, b = self.reduce(g)
        # add(g, neg(g)) must be (0,0,0): the axis carries are 1 exactly
        # when the axis coordinate is nonzero.
        t = (s + self.c1 * (1 if a else 0) + self.c2 * (1 if b else 0)) % 2
        return (t, (-a) % self.ell, (-b) % self.m)

    def sub(self, g: tuple[int, int, int], h: tuple[int, int, int]) -> tuple[int, int, int]:
        return self.add(g, self.neg(h))

    # --- cover structure (the XDoubleCoverData fields) ---

    def proj(self, g: tuple[int, int, int]) -> tuple[int, int]:
        s, a, b = self.reduce(g)
        return (a, b)

    @property
    def deck(self) -> tuple[int, int, int]:
        return (1, 0, 0)

    def sec(self, p: tuple[int, int]) -> tuple[int, int, int]:
        return (0, p[0] % self.ell, p[1] % self.m)


CLASSES: tuple[tuple[int, int], ...] = ((1, 0), (0, 1), (1, 1), (0, 0))
CLASS_NAMES = {(1, 0): "x", (0, 1): "y", (1, 1): "mixed", (0, 0): "split"}


# ---------------------------------------------------------------------------
# Twisted lifts and descent covers
# ---------------------------------------------------------------------------


def monomial_order(P: Poly) -> list[tuple[int, ...]]:
    """The deterministic monomial order twist bits refer to."""
    return sorted(P.support)


def twisted_lift(P: Poly, Gc: CoverGroup, eps: tuple[int, ...]) -> Poly:
    """Lift each monomial of `P` to the sheet given by its twist bit."""
    mons = monomial_order(P)
    if len(eps) != len(mons):
        raise ValueError(f"twist length {len(eps)} != weight {len(mons)}")
    support = frozenset((e % 2, a, b) for e, (a, b) in zip(eps, mons))
    return Poly(support=support, group=Gc)


def fiber_sum(Pc: Poly, base: AbelianGroup) -> Poly:
    """Push a cover polynomial down along `proj`, F₂ coefficients."""
    counts: dict[tuple[int, int], int] = {}
    for (s, a, b) in Pc.support:
        counts[(a, b)] = counts.get((a, b), 0) ^ 1
    return Poly(
        support=frozenset(g for g, c in counts.items() if c), group=base
    )


def descent_checks(
    A: Poly, B: Poly, cls: tuple[int, int],
    epsA: tuple[int, ...], epsB: tuple[int, ...],
) -> tuple[CheckMatrices, CoverGroup]:
    """Check matrices of the descent cover of `(A, B)` at extension
    class `cls` and twist `(epsA, epsB)`."""
    ell, m = A.group.orders
    Gc = CoverGroup(ell, m, *cls)
    Ac = twisted_lift(A, Gc, epsA)
    Bc = twisted_lift(B, Gc, epsB)
    checks = bb_check_matrices(Ac, Bc)
    return checks, Gc


def enumerate_covers(wA: int, wB: int, classes=CLASSES):
    """All (class, epsA, epsB) of the descent space."""
    for cls in classes:
        for epsA in itertools.product((0, 1), repeat=wA):
            for epsB in itertools.product((0, 1), repeat=wB):
                yield cls, epsA, epsB


# ---------------------------------------------------------------------------
# Product-model cross-validation (classes (1,0), (0,1), (0,0))
# ---------------------------------------------------------------------------


def product_model(Gc: CoverGroup):
    """The natural product-group model of a non-mixed class, plus the
    element bijection φ: CoverGroup → product model (a group iso).
    Returns `None` for the mixed class."""
    ell, m, c1, c2 = Gc.ell, Gc.m, Gc.c1, Gc.c2
    if (c1, c2) == (1, 0):
        Gp = AbelianGroup((2 * ell, m))
        phi = lambda g: ((g[1] + ell * g[0]) % (2 * ell), g[2])
    elif (c1, c2) == (0, 1):
        Gp = AbelianGroup((ell, 2 * m))
        phi = lambda g: (g[1], (g[2] + m * g[0]) % (2 * m))
    elif (c1, c2) == (0, 0):
        Gp = AbelianGroup((2, ell, m))
        phi = lambda g: g
    else:
        return None
    return Gp, phi


# ---------------------------------------------------------------------------
# SAT verdicts (thin drivers over bb_lab.sat_distance internals)
# ---------------------------------------------------------------------------


def code_k(checks: CheckMatrices) -> int:
    return checks.num_qubits - int(rank_f2(checks.H_X)) - int(rank_f2(checks.H_Z))


def witness_leq(checks: CheckMatrices, w: int, L_Z: np.ndarray | None = None):
    """One SAT probe: a nontrivial X-logical of weight ≤ w, or None
    (= UNSAT, i.e. d_X > w)."""
    if L_Z is None:
        L_Z = find_logical_z(checks)
    v, _ = _solve_at_weight(checks.H_Z, L_Z, w)
    return v


def exact_distance(
    checks: CheckMatrices, cap: int, L_Z: np.ndarray | None = None,
) -> tuple[int | None, np.ndarray | None]:
    """Exact d_X by the UNSAT ladder from weight 1, giving up above
    `cap`.  Returns (d, witness) or (None, None) if d > cap."""
    if L_Z is None:
        L_Z = find_logical_z(checks)
    for w in range(1, cap + 1):
        v = witness_leq(checks, w, L_Z)
        if v is not None:
            return int(v.sum()), v
    return None, None


# ---------------------------------------------------------------------------
# The screen driver
# ---------------------------------------------------------------------------


def _row_key(row: dict) -> tuple:
    return (tuple(row["cls"]), tuple(row["epsA"]), tuple(row["epsB"]))


def screen_base(
    base_id: str,
    A: Poly,
    B: Poly,
    d_base: int,
    k_base: int,
    out_path: Path,
    classes=CLASSES,
    exact: bool = True,
) -> list[dict]:
    """Fail-fast descent screen of one base.  Appends one JSON line per
    cover to `out_path`; covers already present are skipped (resume)."""
    target = 2 * d_base
    done: set[tuple] = set()
    rows: list[dict] = []
    if out_path.exists():
        for line in out_path.read_text().splitlines():
            if line.strip():
                row = json.loads(line)
                done.add(_row_key(row))
                rows.append(row)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    n_total = 0
    with out_path.open("a") as fh:
        for cls, epsA, epsB in enumerate_covers(
            len(A.support), len(B.support), classes
        ):
            n_total += 1
            key = (cls, epsA, epsB)
            if key in done:
                continue
            t0 = time.time()
            checks, Gc = descent_checks(A, B, cls, epsA, epsB)
            assert_css_commutation(checks)
            k = code_k(checks)
            row: dict = {
                "base_id": base_id,
                "cls": list(cls),
                "cls_name": CLASS_NAMES[cls],
                "epsA": list(epsA),
                "epsB": list(epsB),
                "k": k,
            }
            if k == 0:
                row["verdict"] = "k_zero"
            elif k != k_base:
                # Not a doubling candidate; still record its distance
                # verdict for the census (probe only, no exact refine).
                L_Z = find_logical_z(checks)
                v = witness_leq(checks, target - 1, L_Z)
                row["verdict"] = "k_drop"
                row["d_ub"] = int(v.sum()) if v is not None else None
            else:
                L_Z = find_logical_z(checks)
                v = witness_leq(checks, target - 1, L_Z)
                if v is not None:
                    row["verdict"] = "fail"
                    w0 = int(v.sum())
                    if exact:
                        d, vex = exact_distance(checks, w0, L_Z)
                        row["d"] = d
                        row["witness"] = [int(i) for i in np.flatnonzero(vex)]
                    else:
                        row["d_ub"] = w0
                        row["witness"] = [int(i) for i in np.flatnonzero(v)]
                else:
                    v12 = witness_leq(checks, target, L_Z)
                    if v12 is not None:
                        row["verdict"] = "rescue"
                        row["d"] = target  # UNSAT@target-1 + SAT@target
                        row["witness"] = [int(i) for i in np.flatnonzero(v12)]
                    else:
                        row["verdict"] = "super"  # d > 2*d_base
                        row["d_lb"] = target + 1
            row["secs"] = round(time.time() - t0, 2)
            fh.write(json.dumps(row) + "\n")
            fh.flush()
            rows.append(row)
            print(
                f"[{base_id}] {CLASS_NAMES[cls]:>5} epsA={''.join(map(str,epsA))} "
                f"epsB={''.join(map(str,epsB))}  k={k:>2}  "
                f"{row['verdict']:<7} d={row.get('d', row.get('d_ub', '—'))} "
                f"({row['secs']}s)",
                flush=True,
            )
    return rows


def summarize(rows: list[dict], d_base: int) -> dict:
    by = lambda v: [r for r in rows if r["verdict"] == v]
    out = {
        "covers": len(rows),
        "rescue": len(by("rescue")),
        "super": len(by("super")),
        "fail": len(by("fail")),
        "k_drop": len(by("k_drop")),
        "k_zero": len(by("k_zero")),
        "max_d_fail": max((r.get("d") or r.get("d_ub") or 0) for r in rows) if rows else None,
    }
    per_cls: dict[str, dict] = {}
    for r in rows:
        c = per_cls.setdefault(r["cls_name"], {"rescue": 0, "fail": 0, "other": 0})
        c["rescue" if r["verdict"] == "rescue" else
          "fail" if r["verdict"] == "fail" else "other"] += 1
    out["per_class"] = per_cls
    return out


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main() -> None:
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)

    sc = sub.add_parser("screen", help="descent screen of one base")
    sc.add_argument("--ell", type=int, required=True)
    sc.add_argument("--m", type=int, required=True)
    sc.add_argument("--A", required=True)
    sc.add_argument("--B", required=True)
    sc.add_argument("--base-id", required=True)
    sc.add_argument("--d-base", type=int, required=True)
    sc.add_argument("--k-base", type=int, required=True)
    sc.add_argument("--out", type=Path, required=True)
    sc.add_argument("--no-exact", action="store_true")

    tc = sub.add_parser("toric", help="toric warm-up screen")
    tc.add_argument("--L", type=int, required=True)

    args = ap.parse_args()
    if args.cmd == "screen":
        H = AbelianGroup((args.ell, args.m))
        rows = screen_base(
            args.base_id,
            Poly.from_string(args.A, H),
            Poly.from_string(args.B, H),
            args.d_base,
            args.k_base,
            args.out,
            exact=not args.no_exact,
        )
        print(json.dumps(summarize(rows, args.d_base), indent=2))
    elif args.cmd == "toric":
        L = args.L
        H = AbelianGroup((L, L))
        A = Poly.from_string("1 + x", H)
        B = Poly.from_string("1 + y", H)
        out = LAB_ROOT / "data" / "a10" / f"toric{L}_descent_screen.jsonl"
        rows = screen_base(f"toric{L}", A, B, L, 2, out)
        print(json.dumps(summarize(rows, L), indent=2))


if __name__ == "__main__":
    main()
