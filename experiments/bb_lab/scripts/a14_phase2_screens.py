"""A14 Phase 2: S1+ (pair descent) and S2 (unit-sector kills) screens.

Runs the two next-tier necessary screens on the Phase-1 residual gap
(`data/a14/phase2_gap_rows.jsonl`, 128 rows where S0/S1 missed a light
safe class) and on the live targets (hit3/4/6 y-covers, bb_288 both
axes).  Both screens are certificate-producing: every tried element is
explicitly `seamC(zeta) + d2(f)` for a constructed `f`, so a weight
below `2*d(base)` refutes the safe floor outright (plan §3/§4).

- **S1+**: greedy descent over single AND pair boundary-generator moves
  (<= |G| + C(|G|,2) candidates per round).
- **S2**: CRT block kills.  The odd parts of the frames in play are
  products of Z_q, q in {1,3,5,7,9}; x^q - 1 factors (hardcoded table,
  verified at runtime) give per-coordinate idempotents, tensored into an
  orthogonal idempotent decomposition 1 = sum e_chi of F2[G].  Per block
  and class we solve, inside the ideal e_chi.R, for f_chi killing the
  A-coordinate, the B-coordinate, or both, of the seam's chi-component
  (linear algebra; a kill may be unavailable), enumerate the per-block
  option combos, and S1+-polish the best few.  This is the
  "ideal/character-theoretic" tier OQ4 asked for, in its cheapest
  certified form.

Soundness invariant (asserted where ground truth exists): no screen
value may dip below the exact coset minimum.

Run from `experiments/bb_lab/`:
    uv run python scripts/a14_phase2_screens.py
"""

from __future__ import annotations

import itertools
import json
import sys
import time
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from a14_safe_floor_screens import (  # noqa: E402
    XCover, canonical_row, conv_matrix, parse_poly)
from bb_lab.linalg import nullspace_f2, rref_f2  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]

# ------------------------------------------------------- F2[z] as int polys


def pmul(a: int, b: int) -> int:
    r = 0
    while b:
        if b & 1:
            r ^= a
        a <<= 1
        b >>= 1
    return r


def pdivmod(a: int, b: int) -> tuple[int, int]:
    q = 0
    db = b.bit_length()
    while a.bit_length() >= db:
        s = a.bit_length() - db
        q ^= 1 << s
        a ^= b << s
    return q, a


def pegcd(a: int, b: int) -> tuple[int, int, int]:
    """g, u, v with u*a + v*b = g over F2[z]."""
    r0, r1, s0, s1, t0, t1 = a, b, 1, 0, 0, 1
    while r1:
        q, r = pdivmod(r0, r1)
        r0, r1 = r1, r
        s0, s1 = s1, s0 ^ pmul(q, s1)
        t0, t1 = t1, t0 ^ pmul(q, t1)
    return r0, s0, t0


# x^q - 1 factorizations over F2 (q odd; verified at import below)
ODD_FACTORS = {
    1: [0b11],                       # x + 1  (x^1 - 1 itself)
    3: [0b11, 0b111],
    5: [0b11, 0b11111],
    7: [0b11, 0b1011, 0b1101],
    9: [0b11, 0b111, 0b1001001],
}
for q, fs in ODD_FACTORS.items():
    prod = 1
    for f in fs:
        prod = pmul(prod, f)
    assert prod == (1 << q) | 1, f"bad factor table for q={q}"


def cyclic_idempotents(q: int) -> list[int]:
    """Primitive idempotents of F2[z]/(z^q - 1), as int polys of deg < q."""
    if q == 1:
        return [1]
    modulus = (1 << q) | 1
    out = []
    for f in ODD_FACTORS[q]:
        h, _ = pdivmod(modulus, f)
        g, u, _ = pegcd(h, f)
        assert g == 1
        e = pdivmod(pmul(h, u), modulus)[1]
        assert pdivmod(pmul(e, e), modulus)[1] == e
        out.append(e)
    acc = 0
    for e in out:
        acc ^= e
    assert acc == 1, "idempotents must sum to 1"
    return out


def odd_part(n: int) -> tuple[int, int]:
    a = 1
    while n % 2 == 0:
        n //= 2
        a *= 2
    return a, n  # (2-part, odd part)


def block_idempotent_supports(l: int, m: int) -> list[list[tuple[int, int]]]:
    """Orthogonal idempotent decomposition of F2[Z_l x Z_m] from the odd part.

    Returns one support list per block e_chi = e_i^{(x)} * e_j^{(y)}.
    """
    ax, qx = odd_part(l)
    ay, qy = odd_part(m)
    ex = cyclic_idempotents(qx)  # polys in the order-qx subgroup gen'd by l/qx
    ey = cyclic_idempotents(qy)
    gx, gy = l // qx, m // qy
    blocks = []
    for ei in ex:
        sx = [(k * gx) % l for k in range(qx) if (ei >> k) & 1]
        for ej in ey:
            sy = [(k * gy) % m for k in range(qy) if (ej >> k) & 1]
            blocks.append([(a, b) for a in sx for b in sy])
    return blocks


# ------------------------------------------------------------ linear solves


def solve_f2(S: np.ndarray, t: np.ndarray) -> np.ndarray | None:
    """One solution u of S u = t over F2, or None if inconsistent."""
    aug = np.hstack([S & 1, (t & 1).reshape(-1, 1)]).astype(np.uint8)
    R, piv = rref_f2(aug)
    ncols = S.shape[1]
    u = np.zeros(ncols, dtype=np.uint8)
    for r, c in enumerate(piv):
        if c == ncols:
            return None  # pivot in the augmented column
        u[c] = R[r, ncols]
    return u


# ------------------------------------------------------------ the screens


def s1plus_descent(seam: np.ndarray, moves: np.ndarray,
                   max_rounds: int = 400) -> int:
    cur = seam.copy()
    w = int(cur.sum())
    for _ in range(max_rounds):
        ws = (cur[None, :] ^ moves).sum(axis=1)
        j = int(ws.argmin())
        if int(ws[j]) >= w:
            return w
        cur ^= moves[j]
        w = int(ws[j])
    return w


def pair_moves(gens: np.ndarray, cap: int = 150) -> np.ndarray:
    """Single + pair boundary-generator moves (pairs capped for big |G|)."""
    n = gens.shape[0]
    if n <= cap:
        pairs = [gens[i] ^ gens[j] for i, j in itertools.combinations(range(n), 2)]
        return np.vstack([gens] + [np.stack(pairs)]) if pairs else gens
    return gens  # pairs too many; singles only


class S2Blocks:
    """Per-frame CRT block data for the S2 kill screen."""

    def __init__(self, cov: XCover):
        self.cov = cov
        nb, m = cov.nb, cov.m
        self.E = []       # projection matrices e_chi *
        self.bases = []   # row bases of e_chi R
        for sup in block_idempotent_supports(cov.l, cov.m):
            E = conv_matrix(sup, cov.l, cov.m)
            R, piv = rref_f2(E.T.copy())
            self.E.append(E)
            self.bases.append(R[: len(piv)])
        dims = [b.shape[0] for b in self.bases]
        assert sum(dims) == nb, f"block dims {dims} don't fill {nb}"
        # base-code multiplication matrices (top/bottom halves of d2b)
        self.MAb = cov.d2b[:nb]
        self.MBb = cov.d2b[nb:]

    def kill_options(self, seam: np.ndarray) -> list[list[np.ndarray]]:
        """Per block: list of available f_chi (always includes 0)."""
        nb = self.cov.nb
        s0, s1 = seam[:nb], seam[nb:]
        options = []
        for E, Bas in zip(self.E, self.bases):
            opts = [np.zeros(nb, dtype=np.uint8)]
            SA = (E @ ((self.MAb @ Bas.T) & 1)) & 1   # (nb, r)
            SB = (E @ ((self.MBb @ Bas.T) & 1)) & 1
            tA = (E @ s0) & 1
            tB = (E @ s1) & 1
            for S, t in ((SA, tA), (SB, tB),
                         (np.vstack([SA, SB]), np.concatenate([tA, tB]))):
                u = solve_f2(S, t)
                if u is not None:
                    opts.append((Bas.T @ u) & 1)
            options.append(opts)
        return options

    def best_elements(self, seam: np.ndarray, combo_cap: int = 4096):
        """Enumerate kill combos; return elements sorted by weight."""
        options = self.kill_options(seam)
        total = 1
        for o in options:
            total *= len(o)
        if total > combo_cap:
            options = [o[:2] for o in options]  # degrade gracefully
        elems = []
        for combo in itertools.product(*options):
            f = np.zeros(self.cov.nb, dtype=np.uint8)
            for fc in combo:
                f ^= fc
            elem = seam ^ ((self.cov.d2b @ f) & 1)
            elems.append((int(elem.sum()), elem))
        elems.sort(key=lambda t: t[0])
        return elems


def screen_row_phase2(A, B, l, m, axis, d_base, polish_top: int = 6):
    Ac, Bc, lc, mc = canonical_row(A, B, l, m, axis)
    cov = XCover(Ac, Bc, lc, mc)
    ker = nullspace_f2(cov.d2b)
    kappa = ker.shape[0]
    floor = 2 * d_base
    gens = cov.d2b.T
    moves = pair_moves(gens)
    s2 = S2Blocks(cov)
    per_class = []
    for bits in range(1, 1 << kappa):
        z = np.zeros(cov.nb, dtype=np.uint8)
        for i in range(kappa):
            if (bits >> i) & 1:
                z ^= ker[i]
        seam = cov.seam(z)
        w_s1p = s1plus_descent(seam, moves)
        elems = s2.best_elements(seam)
        w_s2 = elems[0][0]
        w_s2p = min(s1plus_descent(e, moves) for _, e in elems[:polish_top])
        per_class.append({"raw": int(seam.sum()), "s1p": w_s1p,
                          "s2": int(w_s2), "s2p": int(w_s2p)})
    best = {k: min(c[k] for c in per_class) for k in ("raw", "s1p", "s2", "s2p")}
    overall = min(best["s1p"], best["s2p"])
    return {"floor": floor, "dim_ker_d2": kappa, "per_class": per_class,
            "best": best, "min_reached": overall,
            "reject": overall < floor}


# ------------------------------------------------------------------ driver


def main() -> None:
    t0 = time.time()
    gap = [json.loads(line)
           for line in open(ROOT / "data/a14/phase2_gap_rows.jsonl")]
    print(f"== S1+/S2 over the {len(gap)} Phase-1 gap rows ==")
    caught, unsound = 0, 0
    out_rows = []
    for i, r in enumerate(gap):
        rec = screen_row_phase2(parse_poly(r["A"]), parse_poly(r["B"]),
                                r["ell"], r["m"], r["axis"], r["d_base"])
        # soundness: screens can never beat the exact minimum
        for c, e in zip(rec["per_class"], r["exact_minima"]):
            if min(c["s1p"], c["s2p"]) < e:
                unsound += 1
                print(f"  UNSOUND at {r['instance_id']}:{r['axis']} "
                      f"class min {c} < exact {e}")
        caught += rec["reject"]
        out_rows.append({**{k: r[k] for k in
                            ("instance_id", "group", "axis", "verdict")},
                         **rec})
        if (i + 1) % 32 == 0:
            print(f"  ... {i + 1}/{len(gap)} ({time.time() - t0:.0f}s), "
                  f"caught so far {caught}")
    with open(ROOT / "data/a14/phase2_screens.jsonl", "w") as fh:
        for r in out_rows:
            fh.write(json.dumps(r) + "\n")

    print(f"\ngap rows caught by S1+/S2: {caught}/{len(gap)} "
          f"({100 * caught / len(gap):.0f}%); soundness violations {unsound}")
    from collections import Counter
    resid = Counter(f"{r['group']}:{r['axis']}"
                    for r in out_rows if not r["reject"])
    print(f"still-uncaught by frame: {dict(resid)}")

    # cumulative power including Phase 1
    n_sf_false, n_caught_p1 = 506, 378
    print(f"cumulative power: {n_caught_p1 + caught}/{n_sf_false} "
          f"({100 * (n_caught_p1 + caught) / n_sf_false:.0f}%)")

    # ---------------- live targets
    print("\n== live targets ==")
    targets = [
        ("hit3-y  [[72,12,6]]", "y^3 + x + x^2", "y + x*y^2 + x^2", 6, 6, "y", 6),
        ("hit4-y  [[72,12,6]]", "y^3 + x + x^2", "y^2 + x*y^3 + x^2*y", 6, 6, "y", 6),
        ("hit6-y  [[72,12,6]]", "y^3 + x + x^2", "x*y + x^2*y^2 + x^3", 6, 6, "y", 6),
        ("gross-x [[72,12,6]]", "x^3 + y + y^2", "y^3 + x + x^2", 6, 6, "x", 6),
        ("bb288-x [[288,12,18]]", "x^3 + y^2 + y^7", "y^3 + x + x^2", 12, 12, "x", 18),
        ("bb288-y [[288,12,18]]", "x^3 + y^2 + y^7", "y^3 + x + x^2", 12, 12, "y", 18),
    ]
    target_recs = []
    for name, As, Bs, l, m, axis, d in targets:
        rec = screen_row_phase2(parse_poly(As), parse_poly(Bs), l, m, axis, d,
                                polish_top=4)
        target_recs.append({"name": name, **rec})
        print(f"  {name}: floor {rec['floor']}, best "
              f"{ {k: rec['best'][k] for k in ('raw', 's1p', 's2', 's2p')} }, "
              f"min {rec['min_reached']}, reject {rec['reject']}")
    with open(ROOT / "data/a14/phase2_targets.jsonl", "w") as fh:
        for r in target_recs:
            fh.write(json.dumps(r) + "\n")

    ok = unsound == 0
    # gross must never be rejected (proven SF-true)
    for r in target_recs:
        if r["name"].startswith("gross") and r["reject"]:
            ok = False
            print("GROSS FALSE REJECTION — bug")
    print(f"\n{'PHASE 2 SCREEN PASS' if ok else 'PHASE 2 SCREEN FAILED'} "
          f"({time.time() - t0:.0f}s)")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
