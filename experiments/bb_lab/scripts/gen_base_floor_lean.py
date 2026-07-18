#!/usr/bin/env python3
"""T2 generator: parametric Lean base-floor instances (`SmallCycleData`).

For each pilot BB code (ell, m, A, B) this script:

1. **Validates offline** the four finite obligations of the Lean bundle
   `Quantum.Stabilizer.Homological.BB.SmallCycleData` (defined in
   `QEC/Stabilizer/Framework/Homological/BBSmallCycle.lean`), so the
   emitted `native_decide`s are known-true before any Lean build:

   - `epsA` / `epsB`: the polynomial supports have odd size
     (augmentation = 1);
   - `check_two`: no *normalized* weight-2 cycle — for each block b, the
     origin qubit ((0,0),b) plus any single other qubit has nonzero
     syndrome;
   - `check_four`: no normalized weight-4 cycle — origin qubit plus any
     3-subset has nonzero syndrome.  (The Lean statement quantifies over
     *tuples*; colliding tuples cancel in char 2 down to the weight-2
     shape, so subset validation + check_two covers the tuple form.)

   Repo convention (`BBChainComplex.lean`): `∂₁ c = B⋆c_L + A⋆c_R`, so the
   syndrome of a left-block qubit at g is `h ↦ B(h−g)` and of a
   right-block qubit `h ↦ A(h−g)`.  **Repo-left = lab-right.**

   By the class small-cycle theorem (A16 write-up of record;
   `a15_class_certify.py`) all four pilots are certified members, so the
   sweeps must come back clean; a failure here means a data-entry bug.

2. **Emits** `QEC/Stabilizer/Codes/BivariateBicycle/BaseFloors/<Name>.lean`
   instantiating the bundle (obligations by `native_decide`) and exporting
   the floor corollaries, plus the `BaseFloors.lean` umbrella.

Telemetry printed per pilot: n, k (= 2·(|G| − rank[A|B])), and the
validation counts.

Usage:  uv run python scripts/gen_base_floor_lean.py [--check-only]
(from experiments/bb_lab/; repo-relative paths are resolved from the
script location).
"""

from __future__ import annotations

import argparse
import sys
from itertools import combinations
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]
OUT_DIR = REPO / "QEC" / "Stabilizer" / "Codes" / "BivariateBicycle" / "BaseFloors"

# (name, ell, m, A_str, B_str, params_comment, distance_note)
PILOTS = [
    ("BB108", 9, 6, "x^3 + y + y^2", "y^3 + x + x^2", "[[108,8,10]]",
     "True SAT distance d = 10; the class theorem certifies the analytic floor 6."),
    ("BB90", 15, 3, "x^9 + y + y^2", "1 + x^2 + x^7", "[[90,8,10]]",
     "True SAT distance d = 10; the class theorem certifies the analytic floor 6."),
    ("Z6Z14", 6, 14, "1 + y + x^3*y^3", "1 + x + x^2*y^7", "[[168,12,6]]",
     "SAT distance d = 6, so the floor is tight (first analytic member off "
     "the Z3xZ3 odd-part family)."),
]


def parse_poly(s: str, ell: int, m: int) -> list[tuple[int, int]]:
    """Parse '1 + y + x^3*y^3' into sorted [(i, j)] exponent pairs."""
    pts = set()
    for term in s.replace(" ", "").split("+"):
        i = j = 0
        if term != "1":
            for factor in term.split("*"):
                if factor == "x":
                    i += 1
                elif factor == "y":
                    j += 1
                elif factor.startswith("x^"):
                    i += int(factor[2:])
                elif factor.startswith("y^"):
                    j += int(factor[2:])
                else:
                    raise ValueError(f"bad factor {factor!r} in {s!r}")
        pts.add((i % ell, j % m))
    if len(pts) != len(s.replace(" ", "").split("+")):
        raise ValueError(f"repeated support point in {s!r}")
    return sorted(pts)


def gf2_rank(rows: list[int]) -> int:
    rank = 0
    for row in rows:
        cur = row
        for piv in rows[:rank]:
            cur = min(cur, cur ^ piv)
        if cur:
            rows[rank] = cur
            rank += 1
            for i in range(rank - 1, 0, -1):
                if rows[i] > rows[i - 1]:
                    rows[i], rows[i - 1] = rows[i - 1], rows[i]
                else:
                    break
    return rank


def bb_k(ell: int, m: int, A: list[tuple[int, int]], B: list[tuple[int, int]]) -> int:
    """k = 2·(|G| − rank [A | B]) over GF(2)."""
    n = ell * m
    idx = lambda i, j: (i % ell) * m + (j % m)
    rows = []
    for gi in range(ell):
        for gj in range(m):
            row = 0
            for (ai, aj) in A:
                row |= 1 << idx(gi + ai, gj + aj)
            for (bi, bj) in B:
                row |= 1 << (n + idx(gi + bi, gj + bj))
            rows.append(row)
    return 2 * (n - gf2_rank(rows))


def validate(name: str, ell: int, m: int,
             A: list[tuple[int, int]], B: list[tuple[int, int]]) -> dict:
    """Check the four bundle obligations; raise on any violation."""
    n = ell * m
    idx = lambda i, j: (i % ell) * m + (j % m)

    # eps: odd support size
    assert len(A) % 2 == 1 and len(B) % 2 == 1, f"{name}: even polynomial weight"

    # syndrome bitmask of each qubit q = ((gi,gj), blk):
    # blk 0 (left) -> h ↦ B(h−g);  blk 1 (right) -> h ↦ A(h−g)
    synd: dict[tuple[int, int, int], int] = {}
    for gi in range(ell):
        for gj in range(m):
            sl = sr = 0
            for (bi, bj) in B:
                sl |= 1 << idx(gi + bi, gj + bj)
            for (ai, aj) in A:
                sr |= 1 << idx(gi + ai, gj + aj)
            synd[(gi, gj, 0)] = sl
            synd[(gi, gj, 1)] = sr

    points = sorted(synd)
    n2 = n4 = 0
    for b in (0, 1):
        origin = (0, 0, b)
        s0 = synd[origin]
        others = [q for q in points if q != origin]
        for q in others:
            n2 += 1
            if s0 ^ synd[q] == 0:
                raise AssertionError(f"{name}: weight-2 cycle {origin},{q}")
        svals = [synd[q] for q in others]
        for c in combinations(range(len(others)), 3):
            n4 += 1
            if s0 ^ svals[c[0]] ^ svals[c[1]] ^ svals[c[2]] == 0:
                raise AssertionError(
                    f"{name}: weight-4 cycle {origin} + "
                    f"{[others[i] for i in c]}")
    return {"n": 2 * n, "k": bb_k(ell, m, A, B), "pairs": n2, "triples": n4}


def lean_disjunction(pts: list[tuple[int, int]]) -> str:
    return " ∨ ".join(f"g = ({i}, {j})" for i, j in pts)


TEMPLATE = """/-
# Class base floor: {label} = {params} on `Z{ell} × Z{m}` — d ≥ 6 in strong form

Instance of the parametric small-cycle bundle
(`Framework/Homological/BBSmallCycle.lean`): every nonzero 1-cycle of the
{label} complex has weight ≥ 6.  Exported corollaries: the chain floor on
nontrivial cycles, the dual floor, the Pauli-level logical floor, and the
stabilizer-weight floor.

The code is a certified member of the class small-cycle theorem
(A16 write-up of record; certifier
`experiments/bb_lab/scripts/a15_class_certify.py`), so the four finite
obligations discharged below by `native_decide` are its engineering-grade
leaves.
{distance_note}

Polynomials (exponent pairs (x, y)): `A = {A_str}`, `B = {B_str}`.

Generated by `experiments/bb_lab/scripts/gen_base_floor_lean.py`; the
polynomial data is machine-written — regenerate rather than hand-edit.
-/

import QEC.Stabilizer.Framework.Homological.BBSmallCycle

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace {name}

/-- The group `Z{ell} × Z{m}`. -/
abbrev {gname} : Type := ZMod {ell} × ZMod {m}

/-- `A = {A_str}`. -/
def {aname} : {gname} → ZMod 2 := fun g =>
  if {A_disj} then 1 else 0

/-- `B = {B_str}`. -/
def {bname} : {gname} → ZMod 2 := fun g =>
  if {B_disj} then 1 else 0

/-- The {label} chain complex. -/
noncomputable def {cname} : HomologicalCode := bbChainComplex {aname} {bname}

theorem {cname}_numQubits : {cname}.numQubits = {n} := by
  change bbNumQubits {gname} = {n}
  unfold bbNumQubits
  rw [Fintype.card_prod, ZMod.card, ZMod.card]

/-! The four finite obligations, one declaration each (each `native_decide`
gets its own heartbeat budget — bundling them into the structure literal
blows the single-declaration limit on the larger groups). -/

/-- `ε(A) = 1`. -/
lemma epsA_holds : ∑ h : {gname}, {aname} h = 1 := by native_decide

/-- `ε(B) = 1`. -/
lemma epsB_holds : ∑ h : {gname}, {bname} h = 1 := by native_decide

/-- No normalized weight-2 cycle. -/
lemma check_two_holds : ∀ b : Fin 2, ∀ q : {gname} × Fin 2,
    q ≠ ((0 : {gname}), b) →
    ∃ h : {gname}, SmallCycle.termAt {aname} {bname} ((0 : {gname}), b) h
      + SmallCycle.termAt {aname} {bname} q h ≠ 0 := by
  native_decide

/-- No normalized weight-4 cycle (tuple form; colliding tuples cancel to
the weight-2 shape). -/
lemma check_four_holds : ∀ b : Fin 2, ∀ q₁ q₂ q₃ : {gname} × Fin 2,
    q₁ = ((0 : {gname}), b) ∨ q₂ = ((0 : {gname}), b) ∨
    q₃ = ((0 : {gname}), b) ∨
    ∃ h : {gname}, SmallCycle.termAt {aname} {bname} ((0 : {gname}), b) h
      + SmallCycle.termAt {aname} {bname} q₁ h
      + SmallCycle.termAt {aname} {bname} q₂ h
      + SmallCycle.termAt {aname} {bname} q₃ h ≠ 0 := by
  native_decide

/-- The small-cycle bundle: the four finite obligations, machine-checked. -/
def floorData : SmallCycleData {gname} where
  A := {aname}
  B := {bname}
  epsA := epsA_holds
  epsB := epsB_holds
  check_two := check_two_holds
  check_four := check_four_holds

lemma floorData_complex : floorData.complex = {cname} := rfl

/-- **Strong small-cycle floor**: every nonzero 1-cycle of the {label}
complex has weight ≥ 6 — boundaries included. -/
theorem strong_floor (u : {gname} × Fin 2 → ZMod 2)
    (hcyc : bbBoundary1Fn {aname} {bname} u = 0) (hne : u ≠ 0) :
    6 ≤ (Finset.univ.filter fun p => u p ≠ 0).card :=
  floorData.cycle_weight_ge_6 u hcyc hne

/-- Chain-level d ≥ 6 on nontrivial cycles. -/
theorem chain_floor :
    ∀ u ∈ {cname}.cycles, u ∉ {cname}.boundaries →
      6 ≤ {cname}.chainWeight u :=
  floorData.chain_floor

/-- Dual-side chain floor (via the Φ duality). -/
theorem dual_chain_floor :
    ∀ c ∈ {cname}.dualCycles, c ∉ {cname}.dualBoundaries →
      6 ≤ {cname}.chainWeight c :=
  floorData.dual_chain_floor

/-- **Pauli-level logical floor**: every nontrivial logical operator of the
{label} homological stabilizer group has weight ≥ 6. -/
theorem logical_weight_ge_6
    (g : NQubitPauliGroupElement {cname}.numQubits)
    (hg : Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
      {cname}.homologicalStabilizerGroup) :
    6 ≤ NQubitPauliGroupElement.weight g :=
  floorData.logical_weight_ge_6 g hg

/-- Nonzero stabilizer chains (images of `∂₂`) also weigh ≥ 6. -/
theorem stab_weight_ge_6 (f : {gname} → ZMod 2)
    (hne : bbBoundary2Fn {aname} {bname} f ≠ 0) :
    6 ≤ (Finset.univ.filter
      fun p => bbBoundary2Fn {aname} {bname} f p ≠ 0).card :=
  floorData.stab_weight_ge_6 f hne

end {name}
end BB
end Homological
end Stabilizer
end Quantum
"""

UMBRELLA = """/-
# Umbrella: class base floors (T2 layer)

Per-instance `SmallCycleData` bundles for certified members of the class
small-cycle theorem (A16).  Generated by
`experiments/bb_lab/scripts/gen_base_floor_lean.py`.
-/

{imports}
"""


def emit(name: str, ell: int, m: int, A_str: str, B_str: str,
         params: str, note: str,
         A: list[tuple[int, int]], B: list[tuple[int, int]]) -> str:
    import textwrap
    suffix = name.lower().removeprefix("bb")
    label = {"BB108": "bb_108", "BB90": "bb_90", "Z6Z14": "bb_z6z14"}[name]
    return TEMPLATE.format(
        name=name, label=label, params=params, ell=ell, m=m,
        distance_note=textwrap.fill(note, width=72), A_str=A_str, B_str=B_str,
        gname=f"G{ell * m}", aname=f"a{suffix}", bname=f"b{suffix}",
        cname=f"{name.lower()}Complex", n=2 * ell * m,
        A_disj=lean_disjunction(A), B_disj=lean_disjunction(B),
    )


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--check-only", action="store_true",
                    help="validate obligations, emit nothing")
    args = ap.parse_args()

    files = []
    for name, ell, m, A_str, B_str, params, note in PILOTS:
        A = parse_poly(A_str, ell, m)
        B = parse_poly(B_str, ell, m)
        stats = validate(name, ell, m, A, B)
        print(f"{name}: {params} on Z{ell}xZ{m}  n={stats['n']} "
              f"k={stats['k']}  check_two={stats['pairs']} pairs OK, "
              f"check_four={stats['triples']} triples OK")
        if not args.check_only:
            path = OUT_DIR / f"{name}.lean"
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(emit(name, ell, m, A_str, B_str, params, note, A, B))
            files.append(path)

    if not args.check_only:
        imports = "\n".join(
            f"import QEC.Stabilizer.Codes.BivariateBicycle.BaseFloors.{n}"
            for n, *_ in PILOTS)
        umbrella = OUT_DIR.parent / "BaseFloors.lean"
        umbrella.write_text(UMBRELLA.format(imports=imports))
        files.append(umbrella)
        for f in files:
            print(f"wrote {f.relative_to(REPO)}")


if __name__ == "__main__":
    sys.exit(main())
