"""Lean-packaging data generator for the A17 pick f2a6f17e1c41ff96:y.

Pair: base [[150,8,8]] on Z5 x Z15, A = 1 + y + x, B = x*y^6 + x*y^10 + x^2*y^12
(corpus instance f2a6f17e1c41ff96, d_exact = 8 by SAT, CaDiCaL);
y-cover [[300,8,16]] on Z5 x Z30 (deck (0,15)), literal-lift polynomials.
SF-certified cell (docket_decision.jsonl: CMS UNSAT@14 on the orbit rep,
975.8 s + parity; kissat DRAT cross-proof, 6.85 GB).

All computations in the REPO convention (BBChainComplex.lean):
    d2 f = (A*f | B*f), d1 (cL,cR) = B*cL + A*cR,
    dualBoundary (wL,wR) = MA^T wL + MB^T wR.

Emits (hard asserts; nonzero exit on failure):
  1. parameters (base (150,8), cover (300,8) - k preserved, A12 route open)
     + push_A/push_B descent checks for the literal lift;
  2. the Bezout witness (P, Q) with P*Ac + Q*Bc = 1 + y^15 over
     F2[Z5xZ30] (greedy-sparsified), certifying the deck homotopy (R);
  3. the tight witness u*: the A17 cover ladder's weight-16 witness
     (data/a17/cover_witness.jsonl) is deck-invariant, hence = tau(u*)
     for a weight-8 base logical u*; re-verified here in repo convention
     (base cycle, weight 8, non-boundary; tau(u*) cover non-boundary);
  4. a dual flux witness w on the cover (dual cycle, odd pairing with
     tau(u*)) certifying non-boundaryness for the Lean kernel;
  5. JSON (data/a17/f2a6_z5z30_lean_data.json) + Lean-ready supports.

Usage:  uv run python scripts/gen_f2a6_z5z30_data.py
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

LAB_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LAB_ROOT / "src"))

from bb_lab.group import AbelianGroup
from bb_lab.poly import Poly
from bb_lab.checks import bb_check_matrices, circulant
from bb_lab.codeparams import code_params
from bb_lab.linalg import rank_f2, rref_f2, nullspace_f2

A_STR, B_STR = "1 + y + x", "x*y^6 + x*y^10 + x^2*y^12"
ELL, M = 5, 15           # base Z5 x Z15
DECK = (0, 15)           # deck on the cover Z5 x Z30 (y-doubling)
INSTANCE = "f2a6f17e1c41ff96"

fails: list[str] = []


def check(name: str, cond: bool, detail: str = "") -> bool:
    tag = "PASS" if cond else "FAIL"
    print(f"  [{tag}] {name}" + (f"  -- {detail}" if detail else ""))
    if not cond:
        fails.append(name)
    return cond


def solve_f2(Amat: np.ndarray, b: np.ndarray) -> np.ndarray | None:
    Amat = Amat.astype(np.uint8) % 2
    b = b.astype(np.uint8) % 2
    aug = np.hstack([Amat, b[:, None]])
    R, piv = rref_f2(aug)
    ncols = Amat.shape[1]
    if ncols in piv:
        return None
    x = np.zeros(ncols, dtype=np.uint8)
    for r, c in enumerate(piv):
        x[c] = R[r, ncols]
    return x


def sparsify(w: np.ndarray, gens: np.ndarray, pairing: np.ndarray | None = None
             ) -> np.ndarray:
    """Greedy weight reduction of `w` over the span of `gens` rows,
    preserving `<w, pairing> mod 2` if `pairing` is given."""
    w = w.copy() % 2
    improved = True
    while improved:
        improved = False
        for o in gens:
            if pairing is not None and int((o @ pairing) % 2) != 0:
                continue
            cand = (w ^ o) % 2
            if cand.sum() < w.sum():
                w = cand
                improved = True
    return w


def fmt_support(vec: np.ndarray, G: AbelianGroup) -> list[list[int]]:
    elems = list(G)
    return [list(elems[i]) for i in np.nonzero(vec % 2)[0]]


def lean_disj(support: list[list[int]], var: str = "g") -> str:
    """Z3Z6-style membership literal."""
    return " ∨ ".join(f"{var} = ({x}, {y})" for x, y in support)


# ---------------------------------------------------------------- setup
Gb = AbelianGroup((ELL, M))
Gc = AbelianGroup((ELL, 2 * M))
nb, nc = Gb.cardinality, Gc.cardinality  # 75, 150
Ab = Poly.from_string(A_STR, Gb)
Bb = Poly.from_string(B_STR, Gb)
# literal lift: same (x-exp, y-exp) supports, read in Z5 x Z30
Ac = Poly.from_support(Ab.support, Gc)
Bc = Poly.from_support(Bb.support, Gc)
base_idx = {g: i for i, g in enumerate(Gb)}
cover_idx = {g: i for i, g in enumerate(Gc)}
MAb, MBb = circulant(Ab).astype(np.uint8), circulant(Bb).astype(np.uint8)
MAc, MBc = circulant(Ac).astype(np.uint8), circulant(Bc).astype(np.uint8)
D2b = np.vstack([MAb, MBb]) % 2
D1b = np.hstack([MBb, MAb]) % 2
D2c = np.vstack([MAc, MBc]) % 2
D1c = np.hstack([MBc, MAc]) % 2
DUALc = np.hstack([MAc.T, MBc.T]) % 2

print("== 1. parameters, complexes, descent ==")
chb, chc = bb_check_matrices(Ab, Bb), bb_check_matrices(Ac, Bc)
pb, pc = code_params(chb), code_params(chc)
check("base (n,k) = (150,8)", (pb.n, pb.k) == (150, 8), f"got {(pb.n, pb.k)}")
check("cover (n,k) = (300,8)", (pc.n, pc.k) == (300, 8), f"got {(pc.n, pc.k)}")
check("repo d1 o d2 = 0 (base)", not ((D1b @ D2b) % 2).any())
check("repo d1 o d2 = 0 (cover)", not ((D1c @ D2c) % 2).any())
# fiberSum of the literal lift descends to the base polynomial
proj = lambda g: (g[0], g[1] % M)
for name, pcov, pbase in [("A", Ac, Ab), ("B", Bc, Bb)]:
    push = {}
    for g in Gc:
        if g in pcov.support:
            push[proj(g)] = push.get(proj(g), 0) ^ 1
    got = frozenset(h for h, c in push.items() if c)
    check(f"push_{name} descends", got == pbase.support)
# weight-6 stabilizer generators => StrongBaseFloor 8 is false for the base
wt_gen = int(D2b[:, base_idx[(0, 0)]].sum())
check("base stabilizer generator weight = 6 (< d = 8)", wt_gen == 6,
      f"got {wt_gen}")

# ------------------------------------------------- 2. Bezout witness (R)
print("== 2. Bezout witness P*Ac + Q*Bc = 1 + y^15 ==")
target = np.zeros(nc, dtype=np.uint8)
target[cover_idx[(0, 0)]] ^= 1
target[cover_idx[DECK]] ^= 1
ABmat = np.hstack([MAc, MBc]) % 2
pq = solve_f2(ABmat, target)
check("Bezout solvable (A12: iff k preserved)", pq is not None)
p_supp = q_supp = None
if pq is not None:
    ker_AB = nullspace_f2(ABmat)
    pq = sparsify(pq, ker_AB)
    check("Bezout verifies after sparsify",
          np.array_equal((ABmat @ pq) % 2, target))
    P_vec, Q_vec = pq[:nc], pq[nc:]
    p_supp = fmt_support(P_vec, Gc)
    q_supp = fmt_support(Q_vec, Gc)
    print(f"  |P| = {len(p_supp)}, |Q| = {len(q_supp)}")

# ------------------------------------------------- 3. tight witness u*
print("== 3. tight witness u* from the A17 cover-ladder witness ==")
ladder = None
with open(LAB_ROOT / "data" / "a15" / "cover_witness.jsonl") as fh:
    for line in fh:
        rec = json.loads(line)
        if rec["instance_id"] == INSTANCE and rec["axis"] == "y":
            ladder = rec
            break
assert ladder is not None, "ladder witness record not found"
check("ladder witness weight 16", ladder["weight"] == 16)
sup = ladder["witness_support"]

# decode lab qubit index -> (block, group element); lab block 0 = A-block
# = repo left block (j = 0); the only convention delta is a possible
# global reflection g -> -g (lab H_Z = [MB^T | MA^T] vs repo d1 = B*L + A*R)
elems_c = list(Gc)
def decode(support, refl: bool) -> np.ndarray:
    v = np.zeros(2 * nc, dtype=np.uint8)
    for q in support:
        blk, gi = q // nc, q % nc
        g = elems_c[gi]
        if refl:
            g = Gc.reduce(tuple(-x for x in g))
        v[blk * nc + cover_idx[g]] ^= 1
    return v

v_star = None
for refl in (False, True):
    v = decode(sup, refl)
    if not ((D1c @ v) % 2).any():
        v_star = v
        print(f"  repo-cycle decode found (reflect = {refl})")
        break
check("ladder witness decodes to a repo cover cycle", v_star is not None)

in_span = lambda rows, x: rank_f2(np.vstack([rows, x[None, :] & 1])) == rank_f2(rows)
uL = uR = None
if v_star is not None:
    # deck-invariance: support pairs up under y -> y + 15 within blocks
    shift = np.zeros_like(v_star)
    for blk in range(2):
        for g in Gc:
            gp = Gc.reduce((g[0], g[1] + M))
            shift[blk * nc + cover_idx[gp]] = v_star[blk * nc + cover_idx[g]]
    check("ladder witness is deck-invariant", np.array_equal(v_star, shift))
    # descend through the canonical section (y < 15)
    ustar = np.zeros(2 * nb, dtype=np.uint8)
    for blk in range(2):
        for h in Gb:
            ustar[blk * nb + base_idx[h]] = v_star[blk * nc + cover_idx[h]]
    # tau(u*) must reproduce the ladder witness
    tau_mat = np.zeros((2 * nc, 2 * nb), dtype=np.uint8)
    for g in Gc:
        pg = proj(g)
        for blk in range(2):
            tau_mat[blk * nc + cover_idx[g], blk * nb + base_idx[pg]] = 1
    check("tau(u*) = ladder witness", np.array_equal((tau_mat @ ustar) % 2, v_star))
    check("u* weight 8", int(ustar.sum()) == 8)
    check("u* is a base cycle", not ((D1b @ ustar) % 2).any())
    check("u* not a base boundary", not in_span(D2b.T, ustar))
    check("tau(u*) not a cover boundary", not in_span(D2c.T, v_star))
    uL = fmt_support(ustar[:nb], Gb)
    uR = fmt_support(ustar[nb:], Gb)
    print(f"  u* left: {uL}")
    print(f"  u* right: {uR}")

# ------------------------------------------------- 4. dual flux witness
print("== 4. dual flux witness on the cover ==")
wL = wR = None
if v_star is not None:
    kerD = nullspace_f2(DUALc)
    pair = (kerD @ v_star) % 2
    idx = np.nonzero(pair)[0]
    check("dual cycle with odd pairing exists", idx.size > 0)
    if idx.size:
        w = kerD[idx[0]].astype(np.uint8)
        even_gens = np.array([kerD[i] for i in range(kerD.shape[0])
                              if int((kerD[i] @ v_star) % 2) == 0],
                             dtype=np.uint8)
        w = sparsify(w, even_gens)
        check("w is a dual cycle", not ((DUALc @ w) % 2).any())
        check("<w, tau(u*)> = 1", int((w @ v_star) % 2) == 1)
        wL = fmt_support(w[:nc], Gc)
        wR = fmt_support(w[nc:], Gc)
        print(f"  flux witness weight {int(w.sum())}"
              f" (L {len(wL)} / R {len(wR)})")

# ------------------------------------------------- 5. JSON + Lean literals
out = {
    "instance_id": INSTANCE,
    "axis": "y",
    "A": A_STR, "B": B_STR,
    "base_group": [ELL, M], "cover_group": [ELL, 2 * M], "deck": list(DECK),
    "d_base": 8,
    "d_base_provenance": "corpus DB d_exact (SAT: CaDiCaL witness@8 + UNSAT@7)",
    "sf_provenance": "docket_decision.jsonl: CMS UNSAT@14 orbit rep + parity;"
                     " kissat DRAT cross-proof kissat_f2a6f17e_y_w14.drat.gz",
    "P_support": p_supp,
    "Q_support": q_supp,
    "ustar_left": uL, "ustar_right": uR,
    "flux_left": wL, "flux_right": wR,
}
outp = LAB_ROOT / "data" / "a15" / "f2a6_z5z30_lean_data.json"
outp.write_text(json.dumps(out, indent=1))
print(f"\nwrote {outp}")

print("\n== Lean-ready literals ==")
for name, s in [("P", p_supp), ("Q", q_supp),
                ("uStar.L", uL), ("uStar.R", uR),
                ("flux.L", wL), ("flux.R", wR)]:
    if s is not None:
        print(f"-- {name} ({len(s)} cells):")
        print(f"   {lean_disj(s)}")

print("\n" + "=" * 60)
if fails:
    print(f"RESULT: {len(fails)} FAILURES: {fails}")
    sys.exit(1)
print("RESULT: ALL CHECKS PASS")
