"""A14 Phase 1: necessary safe-floor screens (S0/S1) over the T1 corpus.

Per `notes/A14_safe_floor_criterion_plan.md` §4/§6 Phase 1. For every
k-preserving row of `data/a9/t1_hunt.jsonl` (638 rows; frames all have
<= 24 base cells, so *exact* per-class coset minima are computable by
direct enumeration of `im d2`) plus three anchors (pair72 base, gross
base, bb_288 both axes), this computes:

- **ground truth**: exact safe-class coset minima (min over the coset
  `seamC(zeta) + im d2` of the Hamming weight), hence the true SF flag
  `sf_true := all minima >= 2*d_base`;
- **S0** (raw seam weights): reject iff some class's raw seam weight
  `|seamC(zeta)|` < 2d.  Sound by construction (the raw seam is a coset
  element), so any S0 rejection of an sf_true row is a bug;
- **S1** (greedy single-monomial boundary descent from the raw seam,
  budget = descend until no single boundary generator improves): reject
  iff the reached local minimum < 2d.  Sound for the same reason.

Cross-validation: for the 152 DOUBLES rows the recomputed minima are
compared (as multisets) against the A9 profiles'
`safe_class_minima` / `safe_floor_ok` (`data/a9/t1_profiles.json`).

Outputs `data/a14/t1_screens.jsonl` (one record per row) and prints the
soundness/power summary of plan §5.  Pure numpy; the Z4xZ6 rows sweep
`2^22` boundary vectors each (chunked), whole run ~10 min.

Run from `experiments/bb_lab/`:
    uv run python scripts/a14_safe_floor_screens.py
"""

from __future__ import annotations

import json
import sys
import time
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from bb_lab.linalg import nullspace_f2, rank_f2, rref_f2  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
OUT_DIR = ROOT / "data" / "a14"
OUT_DIR.mkdir(parents=True, exist_ok=True)

# ------------------------------------------------------------ poly parsing


def parse_poly(s: str) -> list[tuple[int, int]]:
    """Parse '1 + y + x*y^3 + x^2' into [(ex, ey), ...] exponent pairs."""
    support: list[tuple[int, int]] = []
    for term in s.replace("−", "-").split("+"):
        term = term.strip()
        ex = ey = 0
        if term != "1":
            for factor in term.split("*"):
                factor = factor.strip()
                var, _, exp = factor.partition("^")
                e = int(exp) if exp else 1
                if var == "x":
                    ex += e
                elif var == "y":
                    ey += e
                else:
                    raise ValueError(f"bad factor {factor!r} in {s!r}")
        support.append((ex, ey))
    return support


# ------------------------------------------------------------ BB machinery


def idx(x: int, y: int, m: int) -> int:
    return x * m + y


def conv_matrix(support, l, m) -> np.ndarray:
    n = l * m
    M = np.zeros((n, n), dtype=np.uint8)
    for (px, py) in support:
        for hx in range(l):
            for hy in range(m):
                M[idx(hx, hy, m), idx((hx - px) % l, (hy - py) % m, m)] ^= 1
    return M


def bb_matrices(A, B, l, m):
    cA, cB = conv_matrix(A, l, m), conv_matrix(B, l, m)
    return np.vstack([cA, cB]), np.hstack([cB, cA])  # d2 (2n x n), d1 (n x 2n)


def h1_dim(d2, d1) -> int:
    return (d1.shape[1] - rank_f2(d1)) - rank_f2(d2)


class XCover:
    """Free Z2 BB cover doubling the *first* coordinate (canonicalized)."""

    def __init__(self, A, B, l, m):
        self.l, self.m, self.nb = l, m, l * m
        self.d2b, self.d1b = bb_matrices(A, B, l, m)
        self.d2c, self.d1c = bb_matrices(A, B, 2 * l, m)

    def seam(self, zeta: np.ndarray) -> np.ndarray:
        """Carry masks of (A~ zeta~, B~ zeta~): the safe-class representative."""
        l, m, nb, nc = self.l, self.m, self.nb, 2 * self.nb
        zl = np.zeros(nc, dtype=np.uint8)
        for x in range(l):
            for y in range(m):
                zl[idx(x, y, m)] = zeta[idx(x, y, m)]
        t = (self.d2c @ zl) & 1
        out = np.zeros(2 * nb, dtype=np.uint8)
        for j in (0, 1):
            for x in range(l):
                for y in range(m):
                    out[j * nb + idx(x, y, m)] = t[j * nc + idx(x + l, y, m)]
        return out


def canonical_row(A, B, l, m, axis):
    """Swap coordinates so the doubled axis is always x."""
    if axis == "x":
        return A, B, l, m
    return ([(ey, ex) for (ex, ey) in A], [(ey, ex) for (ex, ey) in B], m, l)


# ------------------------------------------------------------ the screens


def boundary_basis(d2: np.ndarray) -> np.ndarray:
    """Row basis of im d2 (independent boundary generators)."""
    R, piv = rref_f2(d2.T)
    return R[: len(piv)]


def exact_minima(cover: XCover, seams: list[np.ndarray],
                 chunk_bits: int = 20) -> list[int]:
    """Exact coset minima: sweep all of im d2, chunked GEMM over its basis."""
    Bb = boundary_basis(cover.d2b).astype(np.uint8)
    r, width = Bb.shape
    mins = [seam.sum() for seam in seams]
    total = 1 << r
    step_bits = min(chunk_bits, r)
    step = 1 << step_bits
    lo_bits = np.arange(step, dtype=np.uint64)
    Flo = ((lo_bits[:, None] >> np.arange(step_bits, dtype=np.uint64)[None, :])
           & 1).astype(np.float32)
    # float32 GEMM hits BLAS (integer matmul would not); exact for sums <= 24
    lo_part = (Flo @ Bb[:step_bits].astype(np.float32)).astype(np.uint8) & 1
    for hi in range(total >> step_bits):
        if r > step_bits:
            hi_vec = np.zeros(width, dtype=np.uint8)
            for i in range(r - step_bits):
                if (hi >> i) & 1:
                    hi_vec ^= Bb[step_bits + i]
            block = lo_part ^ hi_vec[None, :]
        else:
            block = lo_part
        for ci, seam in enumerate(seams):
            w = int((block ^ seam[None, :]).sum(axis=1).min())
            if w < mins[ci]:
                mins[ci] = w
    return [int(x) for x in mins]


def greedy_descent(seam: np.ndarray, gens: np.ndarray, max_rounds: int = 200):
    """S1: coordinate descent over single boundary generators."""
    cur = seam.copy()
    w = int(cur.sum())
    for _ in range(max_rounds):
        cand = cur[None, :] ^ gens                     # (n_gens, width)
        ws = cand.sum(axis=1)
        j = int(ws.argmin())
        if int(ws[j]) >= w:
            return w
        cur, w = cand[j], int(ws[j])
    return w


def screen_row(A, B, l, m, axis, d_base, k_expected=None):
    """Run ground truth + S0 + S1 on one (presentation, axis) candidate."""
    Ac, Bc, lc, mc = canonical_row(A, B, l, m, axis)
    cov = XCover(Ac, Bc, lc, mc)
    kb = h1_dim(cov.d2b, cov.d1b)
    kc = h1_dim(cov.d2c, cov.d1c)
    rec = {"k_base_recomputed": kb, "k_cover_recomputed": kc}
    if k_expected is not None and kb != k_expected:
        rec["warn"] = f"k mismatch: file {k_expected}, recomputed {kb}"
    if kc != kb:
        rec["skip"] = "k not preserved ((R) fails); out of SF scope"
        return rec
    ker = nullspace_f2(cov.d2b)
    kappa = ker.shape[0]
    seams, combos = [], []
    for bits in range(1, 1 << kappa):
        z = np.zeros(cov.nb, dtype=np.uint8)
        for i in range(kappa):
            if (bits >> i) & 1:
                z ^= ker[i]
        combos.append(bits)
        seams.append(cov.seam(z))
    floor = 2 * d_base
    raw = [int(s.sum()) for s in seams]
    gens = cov.d2b.T  # single-monomial boundary generators, one per base cell
    desc = [greedy_descent(s, gens) for s in seams]
    rec.update({
        "dim_ker_d2": kappa,
        "floor": floor,
        "s0_raw_weights": raw,
        "s0_reject": min(raw) < floor,
        "s1_descended": desc,
        "s1_reject": min(desc) < floor,
    })
    if cov.nb - kappa <= 22:  # exact sweep feasible (all T1 frames)
        mins = exact_minima(cov, seams)
        rec["exact_minima"] = mins
        rec["sf_true"] = min(mins) >= floor
    return rec


# ------------------------------------------------------------ corpus driver


def main() -> None:
    t0 = time.time()
    rows = [json.loads(line) for line in open(ROOT / "data/a9/t1_hunt.jsonl")]
    profiles = {(p["instance_id"], p["axis"]): p
                for p in json.load(open(ROOT / "data/a9/t1_profiles.json"))}

    out_path = OUT_DIR / "t1_screens.jsonl"
    results = []
    n_bad_xval = 0
    with open(out_path, "w") as fh:
        for i, r in enumerate(rows):
            rec = dict(r)
            rec.update(screen_row(parse_poly(r["A"]), parse_poly(r["B"]),
                                  r["ell"], r["m"], r["axis"], r["d_base"],
                                  k_expected=r["k"]))
            # cross-validate against the A9 profile where one exists
            prof = profiles.get((r["instance_id"], r["axis"]))
            if prof is not None and "exact_minima" in rec:
                same_min = sorted(rec["exact_minima"]) == \
                    sorted(prof["safe_class_minima"])
                same_flag = rec["sf_true"] == prof["safe_floor_ok"]
                rec["xval_profile_ok"] = bool(same_min and same_flag)
                if not rec["xval_profile_ok"]:
                    n_bad_xval += 1
                    print(f"  XVAL MISMATCH {r['instance_id']}:{r['axis']} "
                          f"mine {rec['exact_minima']} vs "
                          f"profile {prof['safe_class_minima']}")
            results.append(rec)
            fh.write(json.dumps(rec) + "\n")
            if (i + 1) % 50 == 0:
                print(f"  ... {i + 1}/{len(rows)} rows "
                      f"({time.time() - t0:.0f}s)")

    # ---------------- anchors (S0/S1 only where exact GT is out of reach)
    anchors = [
        ("pair72-base [[36,4,4]] x", [(2, 0), (0, 1), (0, 3)],
         [(0, 0), (1, 0), (0, 2)], 3, 6, "x", 4, True),
        ("gross-base [[72,12,6]] x", [(3, 0), (0, 1), (0, 2)],
         [(0, 3), (1, 0), (2, 0)], 6, 6, "x", 6, True),
        ("bb_288 [[288,12,18]] x", parse_poly("x^3 + y^2 + y^7"),
         parse_poly("y^3 + x + x^2"), 12, 12, "x", 18, False),
        ("bb_288 [[288,12,18]] y", parse_poly("x^3 + y^2 + y^7"),
         parse_poly("y^3 + x + x^2"), 12, 12, "y", 18, False),
    ]
    print("\n== anchors ==")
    anchor_recs = []
    with open(OUT_DIR / "anchors_screens.jsonl", "w") as fh:
        for name, A, B, l, m, axis, d, sf_known_true in anchors:
            rec = {"name": name}
            rec.update(screen_row(A, B, l, m, axis, d))
            anchor_recs.append((name, rec, sf_known_true))
            fh.write(json.dumps(rec) + "\n")
            if "skip" in rec:
                print(f"  {name}: SKIP ({rec['skip']})")
                continue
            print(f"  {name}: raw min {min(rec['s0_raw_weights'])}, "
                  f"descended min {min(rec['s1_descended'])}, floor "
                  f"{rec['floor']}, S0 reject {rec['s0_reject']}, "
                  f"S1 reject {rec['s1_reject']}"
                  + (f", exact minima {rec['exact_minima']}"
                     if "exact_minima" in rec else ""))

    # ---------------- summary
    scoped = [r for r in results if "sf_true" in r]
    skipped = [r for r in results if "skip" in r]
    doublers = [r for r in scoped if r["verdict"] == "DOUBLES"]
    shorts = [r for r in scoped if r["verdict"] == "short"]
    sf_true = [r for r in scoped if r["sf_true"]]
    sf_false = [r for r in scoped if not r["sf_true"]]

    print("\n================= A14 Phase 1 summary =================")
    print(f"rows {len(rows)} | scoped (k-preserving, exact GT) {len(scoped)} "
          f"| skipped (k changes) {len(skipped)}")
    print(f"profile cross-validation mismatches: {n_bad_xval} (must be 0)")
    print(f"doublers: {len(doublers)} — SF-true "
          f"{sum(r['sf_true'] for r in doublers)} (A11 said 111), "
          f"overlap-rescued {sum(not r['sf_true'] for r in doublers)} "
          f"(A11 said 41)")
    print(f"shorts:   {len(shorts)} — SF-fail "
          f"{sum(not r['sf_true'] for r in shorts)} (A11 said 322)")

    fr_s0 = [r for r in sf_true if r["s0_reject"]]
    fr_s1 = [r for r in sf_true if r["s1_reject"]]
    print(f"\nSOUNDNESS (false rejections on {len(sf_true)} SF-true rows): "
          f"S0 {len(fr_s0)}, S1 {len(fr_s1)}  (both must be 0)")

    n_s0 = sum(r["s0_reject"] for r in sf_false)
    n_s1 = sum(r["s1_reject"] for r in sf_false)
    n_either = sum(r["s0_reject"] or r["s1_reject"] for r in sf_false)
    print(f"\nPOWER on {len(sf_false)} SF-false rows: "
          f"S0 {n_s0} ({100 * n_s0 / max(1, len(sf_false)):.0f}%), "
          f"S0+S1 {n_either} ({100 * n_either / max(1, len(sf_false)):.0f}%)")

    by = {}
    for r in sf_false:
        key = f"{r['group']}:{r['axis']}"
        a, b = by.get(key, (0, 0))
        by[key] = (a + 1, b + (1 if (r["s0_reject"] or r["s1_reject"]) else 0))
    print("  per frame:axis (SF-false, caught):")
    for key in sorted(by):
        a, b = by[key]
        print(f"    {key:12s} {a:4d} {b:4d}  ({100 * b / a:.0f}%)")

    gap = [r for r in sf_false if not (r["s0_reject"] or r["s1_reject"])]
    with open(OUT_DIR / "phase2_gap_rows.jsonl", "w") as fh:
        for r in gap:
            fh.write(json.dumps(r) + "\n")
    print(f"\nresidual gap rows (SF-false, uncaught -> Phase 2 fodder): "
          f"{len(gap)} -> data/a14/phase2_gap_rows.jsonl")

    ok = (n_bad_xval == 0 and not fr_s0 and not fr_s1)
    # anchor sanity: known-SF-true anchors must not be rejected
    for name, rec, sf_known_true in anchor_recs:
        if sf_known_true and "s0_reject" in rec and \
                (rec["s0_reject"] or rec["s1_reject"]):
            ok = False
            print(f"ANCHOR FALSE REJECTION: {name}")
    print(f"\n{'PHASE 1 GATE GREEN' if ok else 'PHASE 1 GATE FAILED'} "
          f"({time.time() - t0:.0f}s)")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
