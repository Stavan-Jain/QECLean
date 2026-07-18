#!/usr/bin/env python
"""a11_cx_verify_m.py — independent verification + sector diagnosis of the
(M)-robustness counterexample candidate from the 2026-07-02 cx hunt.

Target record (data/a11/cx/hunt_big.jsonl):

    frame Z5xZ5,  A = x^2*y + x^3 + x^3*y^3 + x^3*y^4,
                  B = x^4 + x^4*y + x^4*y^2 + x^4*y^4      (weights 4 x 4)
    axis y:  k 2 -> 2, tight witness, Z-side safe floors >= 10,
             d_cover = 8 < 10 = 2*d_base   ->  verdict COUNTEREXAMPLE.

The hunt's numbers all came through the SAT stack, and its safe floors
were computed on the Z side while the failing witness is X-type (the
honesty-ledger side-gap).  This script re-derives every leg with
independent methods and runs the missing check:

  V1  base floor d(base) >= 5 by EXHAUSTIVE enumeration of all
      C(50,1..4) = 251,175 supports on BOTH sides (pure numpy popcount,
      no solver), plus numpy-verified weight-5 witnesses (X and Z sides)
      => d_X(base) = d_Z(base) = 5 exactly.
  V2  cover (y-axis literal lift, Z5xZ10): k preserved by rank; (R)
      pinned concretely via the Bezout membership eps = 1 + y^5 in the
      cover ideal (A, B) (colspace rank test), per the A12 theorem.
  V3  the stored weight-8 witness: in ker H_Z(cover), outside
      rowspace(H_X(cover)), weight 8 (pure numpy) => d_X(cover) <= 8
      < 10.  Independent x_distance re-run from scratch for the exact
      cover value.
  V4  SECTOR DIAGNOSIS of the witness (never run by the hunt): push
      b := p(v); classify b = 0 (diagonal) / b in rowspace(H_X base)
      (DANGEROUS: b != 0 stabilizer rung) / else (SAFE-sector break =>
      the hunt's Z-side-only floors were a side artifact).  Sheet split
      |v| = |b| + 2*overlap recorded.
  V5  X-side safe floors, exhaustive: push the cover X-logical basis,
      reduce mod rowspace(H_X base); every nonzero class combo gets an
      EXACT coset minimum by sweeping the full 2^rank stabilizer coset
      (packed-uint64 popcount).  Closes the side gap left by the hunt.
  V6  Z-side safe floors re-derived the same exhaustive way (the hunt
      used SAT ladders; this replaces them with enumeration).
  V7  tight witness re-check: some translate of the weight-5 base
      Z-logical lifts diagonally to a nontrivial weight-10 cover
      Z-logical.

Usage:   .venv/bin/python scripts/a11_cx_verify_m.py
Writes:  data/a11/cx/verify_m.json
"""

from __future__ import annotations

import itertools
import json
import sys
import time
from pathlib import Path

import numpy as np

LAB_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LAB_ROOT / "src"))
sys.path.insert(0, str(LAB_ROOT / "scripts"))

from bb_lab.checks import bb_check_matrices
from bb_lab.group import AbelianGroup
from bb_lab.linalg import nullspace_f2, rank_f2, quotient_complement_basis
from bb_lab.poly import Poly
from bb_lab.sat_distance import x_distance, find_logical_z, _solve_at_weight

from a9_lean_target_screen import blkdiag, cover_group, cover_maps, lift_poly

CX_DIR = LAB_ROOT / "data" / "a11" / "cx"

FRAME = (5, 5)
A_STR = "x^2*y + x^3 + x^3*y^3 + x^3*y^4"
B_STR = "x^4 + x^4*y + x^4*y^2 + x^4*y^4"
AXIS = "y"


# ---------------------------------------------------------------------------
# F2 helpers (self-contained; no reuse of the hunt's evaluation path)
# ---------------------------------------------------------------------------


class Span:
    """Incremental F2 row span with membership tests."""

    def __init__(self, M: np.ndarray | None = None) -> None:
        self.piv: dict[int, np.ndarray] = {}
        if M is not None:
            for row in M:
                self.add(row)

    def reduce(self, v: np.ndarray) -> np.ndarray:
        v = (v & 1).astype(np.uint8, copy=True)
        while True:
            nz = np.flatnonzero(v)
            if nz.size == 0:
                return v
            p = int(nz[0])
            row = self.piv.get(p)
            if row is None:
                return v
            v ^= row

    def add(self, v: np.ndarray) -> bool:
        r = self.reduce(v)
        nz = np.flatnonzero(r)
        if nz.size == 0:
            return False
        self.piv[int(nz[0])] = r
        return True

    def contains(self, v: np.ndarray) -> bool:
        return not self.reduce(v).any()


def f2_row_basis(M: np.ndarray) -> np.ndarray:
    """Independent-row basis of rowspace(M)."""
    s = Span()
    rows = [r for r in (M & 1).astype(np.uint8) if s.add(r)]
    return np.array(rows, dtype=np.uint8)


def pack_bits(V: np.ndarray) -> np.ndarray:
    """(N, n<=64) uint8 -> (N,) uint64, bit j of word = column j."""
    V = np.atleast_2d(V).astype(np.uint64)
    powers = np.uint64(1) << np.arange(V.shape[1], dtype=np.uint64)
    return (V * powers[None, :]).sum(axis=1, dtype=np.uint64)


def popcount_u64(a: np.ndarray) -> np.ndarray:
    if hasattr(np, "bitwise_count"):
        return np.bitwise_count(a)
    m1 = np.uint64(0x5555555555555555)
    m2 = np.uint64(0x3333333333333333)
    m4 = np.uint64(0x0F0F0F0F0F0F0F0F)
    h  = np.uint64(0x0101010101010101)
    a = a - ((a >> np.uint64(1)) & m1)
    a = (a & m2) + ((a >> np.uint64(2)) & m2)
    a = (a + (a >> np.uint64(4))) & m4
    return (a * h) >> np.uint64(56)


def coset_min_exhaustive(rep: np.ndarray, basis: np.ndarray) -> int:
    """Exact min weight over rep + rowspace(basis), by enumerating the
    entire 2^rank coset as packed uint64 words.  n <= 64 only."""
    arr = pack_bits(rep[None, :])
    for w in pack_bits(basis):
        arr = np.concatenate([arr, arr ^ w])
    return int(popcount_u64(arr).min())


def light_kernel_logicals(H_ker: np.ndarray, H_triv: np.ndarray,
                          wmax: int) -> tuple[int, int, int | None]:
    """Exhaustively enumerate all supports of weight 1..wmax and count
    kernel hits of H_ker, splitting trivial (in rowspace(H_triv)) from
    nontrivial.  Returns (n_trivial, n_nontrivial, min_nontrivial_wt)."""
    n = H_ker.shape[1]
    cols = pack_bits(H_ker.T)          # column syndromes, packed
    triv_span = Span(H_triv)
    n_triv = n_nontriv = 0
    min_wt: int | None = None
    for w in range(1, wmax + 1):
        idx = np.fromiter(
            itertools.chain.from_iterable(itertools.combinations(range(n), w)),
            dtype=np.int64,
        ).reshape(-1, w)
        syn = cols[idx[:, 0]].copy()
        for j in range(1, w):
            syn ^= cols[idx[:, j]]
        for r in np.flatnonzero(syn == 0):
            v = np.zeros(n, dtype=np.uint8)
            v[idx[r]] = 1
            if triv_span.contains(v):
                n_triv += 1
            else:
                n_nontriv += 1
                if min_wt is None:
                    min_wt = w
    return n_triv, n_nontriv, min_wt


def verify_x_logical(v: np.ndarray, HZ: np.ndarray, HX: np.ndarray) -> dict:
    return {
        "weight": int(v.sum()),
        "in_ker_HZ": not ((HZ @ v) % 2).any(),
        "notin_rowspace_HX": not Span(HX).contains(v),
    }


def main() -> None:
    t0 = time.time()
    out: dict = {"frame": "Z5xZ5", "A": A_STR, "B": B_STR, "axis": AXIS}
    Gb = AbelianGroup(FRAME)
    A = Poly.from_string(A_STR, Gb)
    B = Poly.from_string(B_STR, Gb)
    assert A.weight() == 4 and B.weight() == 4
    chb = bb_check_matrices(A, B)
    HXb = chb.H_X.astype(np.uint8)
    HZb = chb.H_Z.astype(np.uint8)
    nb = chb.num_qubits
    assert nb == 50

    # ---- V1: base parameters, exhaustive floor --------------------------
    kb = nb - rank_f2(HXb) - rank_f2(HZb)
    out["V1_k_base"] = int(kb)

    trivX, nontrivX, minX = light_kernel_logicals(HZb, HXb, 4)  # X-type ops
    trivZ, nontrivZ, minZ = light_kernel_logicals(HXb, HZb, 4)  # Z-type ops
    out["V1_exhaustive_le4"] = {
        "X_side": {"trivial": trivX, "nontrivial": nontrivX, "min_wt": minX},
        "Z_side": {"trivial": trivZ, "nontrivial": nontrivZ, "min_wt": minZ},
    }
    floor5 = nontrivX == 0 and nontrivZ == 0

    resb = x_distance(chb, weight_upper_bound=12)
    wx = resb.witness.astype(np.uint8)
    out["V1_dX_base_sat"] = int(resb.distance)
    out["V1_x_witness_check"] = verify_x_logical(wx, HZb, HXb)

    kerZb = nullspace_f2(HZb)
    LXb = quotient_complement_basis(HXb, kerZb)
    witZ, _ = _solve_at_weight(HXb, LXb, 5)
    witZ = None if witZ is None else (witZ & 1).astype(np.uint8)
    out["V1_z_witness_check"] = (
        None if witZ is None
        else {
            "weight": int(witZ.sum()),
            "in_ker_HX": not ((HXb @ witZ) % 2).any(),
            "notin_rowspace_HZ": not Span(HZb).contains(witZ),
        }
    )
    d_base = 5 if (floor5 and out["V1_x_witness_check"]["weight"] == 5) else None
    out["V1_d_base_exact"] = d_base
    print(f"V1  k_base={kb}  exhaustive<=4: X {trivX}/{nontrivX}, "
          f"Z {trivZ}/{nontrivZ}  d_X(sat)={resb.distance}  d_base={d_base}",
          flush=True)

    # ---- V2: cover, k preservation, Bezout (R) --------------------------
    Gc = cover_group(*FRAME, AXIS)
    Ac, Bc = lift_poly(A, Gc), lift_poly(B, Gc)
    chc = bb_check_matrices(Ac, Bc)
    HXc = chc.H_X.astype(np.uint8)
    HZc = chc.H_Z.astype(np.uint8)
    nc = chc.num_qubits
    assert nc == 100
    kc = nc - rank_f2(HXc) - rank_f2(HZc)
    out["V2_k_cover"] = int(kc)

    MAc, MBc = HXc[:, : nc // 2], HXc[:, nc // 2:]
    eps = np.zeros(nc // 2, dtype=np.uint8)
    eps[Gc.index((0, 0))] = 1
    eps[Gc.index((0, FRAME[1]))] = 1          # 1 + y^m  (deck translation)
    stack = np.hstack([MAc, MBc]).T           # rows span colspace
    bez = rank_f2(np.vstack([stack, eps[None, :]])) == rank_f2(stack)
    out["V2_bezout_eps_in_ideal"] = bool(bez)
    print(f"V2  k_cover={kc}  (R)/Bezout eps in (A,B): {bez}", flush=True)

    # ---- V3: the stored weight-8 witness --------------------------------
    rec = None
    with open(CX_DIR / "hunt_big.jsonl") as fh:
        for line in fh:
            r = json.loads(line)
            if r.get("A") == A_STR and r.get("B") == B_STR:
                rec = r
                break
    assert rec is not None, "stored record not found"
    ax = next(a for a in rec["axes"] if a["axis"] == AXIS)
    v = np.array(ax["witness"], dtype=np.uint8)
    assert v.size == nc
    out["V3_stored_witness_check"] = verify_x_logical(v, HZc, HXc)
    resc = x_distance(chc, weight_upper_bound=10)
    out["V3_dX_cover_sat"] = int(resc.distance)
    vfresh = resc.witness.astype(np.uint8)
    out["V3_fresh_witness_check"] = verify_x_logical(vfresh, HZc, HXc)
    print(f"V3  stored witness {out['V3_stored_witness_check']}  "
          f"d_X(cover) sat re-run = {resc.distance}", flush=True)

    # ---- V4: sector diagnosis -------------------------------------------
    p_blk, tau_blk, sig_blk, deck = cover_maps(Gb, Gc, AXIS)
    P = blkdiag(p_blk)
    S = blkdiag(sig_blk)

    def diagnose(vec: np.ndarray, tag: str) -> dict:
        b = (P @ vec) % 2
        d: dict = {"push_weight": int(b.sum()),
                   "push_in_ker_HZb": not ((HZb @ b) % 2).any()}
        if not b.any():
            d["sector"] = "diagonal (p(v) = 0)"
        elif Span(HXb).contains(b):
            d["sector"] = "DANGEROUS (b != 0 stabilizer)"
        else:
            d["sector"] = "SAFE-SECTOR BREAK (nontrivial base class)"
            d["class_coset_min"] = coset_min_exhaustive(b, f2_row_basis(HXb))
        # sheet split
        v0 = np.zeros(nb, dtype=np.uint8)
        v1 = np.zeros(nb, dtype=np.uint8)
        cells = list(Gc)
        half = nc // 2
        for pos in np.flatnonzero(vec):
            blk, j = divmod(int(pos), half)
            h = cells[j]
            gidx = blk * (nb // 2) + Gb.index((h[0] % FRAME[0], h[1] % FRAME[1]))
            if (h[0] // FRAME[0] if AXIS == "x" else h[1] // FRAME[1]) == 0:
                v0[gidx] ^= 1
            else:
                v1[gidx] ^= 1
        d["sheet_weights"] = [int(v0.sum()), int(v1.sum())]
        d["sheet_overlap"] = int((v0 & v1).sum())
        d["deck_invariant"] = bool(((S @ vec) % 2 == vec).all())
        assert ((v0 ^ v1) == b).all()
        print(f"V4  [{tag}] |p(v)|={d['push_weight']}  {d['sector']}  "
              f"sheets={d['sheet_weights']} overlap={d['sheet_overlap']}",
              flush=True)
        return d

    out["V4_sector_stored"] = diagnose(v, "stored")
    if not np.array_equal(vfresh, v):
        out["V4_sector_fresh"] = diagnose(vfresh, "fresh")

    # ---- V5 / V6: safe floors, both sides, exhaustive --------------------
    def safe_floors(L_cover: np.ndarray, H_stab_base: np.ndarray,
                    tag: str) -> dict:
        span = Span(H_stab_base)
        reps = [img.astype(np.uint8) for row in L_cover
                if span.add(img := (P @ row) % 2)]
        basis = f2_row_basis(H_stab_base)
        minima = []
        for mask in range(1, 1 << len(reps)):
            combo = np.zeros(nb, dtype=np.uint8)
            for i in range(len(reps)):
                if (mask >> i) & 1:
                    combo ^= reps[i]
            minima.append(coset_min_exhaustive(combo, basis))
        d = {"rank_p_star": len(reps), "stab_rank": int(basis.shape[0]),
             "coset_minima": minima,
             "floor_ok_ge_10": all(m >= 10 for m in minima)}
        print(f"V{tag}  rank(im p_*)={len(reps)}  2^{basis.shape[0]}-coset "
              f"minima={minima}  floor>=10: {d['floor_ok_ge_10']}", flush=True)
        return d

    kerZc = nullspace_f2(HZc)
    LXc = quotient_complement_basis(HXc, kerZc)      # cover X-logical basis
    out["V5_safe_floors_X"] = safe_floors(LXc, HXb, "5[X]")
    LZc = find_logical_z(chc)                        # cover Z-logical basis
    out["V6_safe_floors_Z"] = safe_floors(LZc, HZb, "6[Z]")

    # ---- V7: tight witness ------------------------------------------------
    tight = None
    if witZ is not None:
        T = blkdiag(tau_blk)
        spanZc = Span(HZc)
        ell, m = FRAME
        half_b = nb // 2
        for g in Gb:
            perm = np.array([Gb.index(((h[0] + g[0]) % ell, (h[1] + g[1]) % m))
                             for h in Gb], dtype=np.int64)
            tr = np.zeros_like(witZ)
            tr[perm] = witZ[:half_b]
            tr[half_b + perm] = witZ[half_b:]
            tau_u = (T @ tr) % 2
            if not ((HXc @ tau_u) % 2).any() and not spanZc.contains(tau_u):
                tight = {"weight": int(tau_u.sum()), "translate": list(g)}
                break
    out["V7_tight_witness"] = tight
    print(f"V7  tight diagonal witness: {tight}", flush=True)

    # ---- verdict -----------------------------------------------------------
    stored_ok = all(out["V3_stored_witness_check"].values())
    csafe_two_sided = (
        out["V1_k_base"] == out["V2_k_cover"] == 2
        and tight is not None
        and out["V5_safe_floors_X"]["floor_ok_ge_10"]
        and out["V6_safe_floors_Z"]["floor_ok_ge_10"]
    )
    dangerous = out["V4_sector_stored"]["sector"].startswith("DANGEROUS")
    confirmed = bool(d_base == 5 and stored_ok and csafe_two_sided and dangerous)
    out["csafe_two_sided"] = csafe_two_sided
    out["verdict_confirmed_counterexample"] = confirmed
    out["elapsed_s"] = round(time.time() - t0, 1)

    CX_DIR.mkdir(parents=True, exist_ok=True)
    (CX_DIR / "verify_m.json").write_text(json.dumps(out, indent=1))
    print(f"\nVERDICT: confirmed_counterexample = {confirmed}   "
          f"(csafe_two_sided={csafe_two_sided}, dangerous_bind={dangerous}, "
          f"d_base={d_base}, d_cover<= {int(v.sum())})   "
          f"[{out['elapsed_s']}s]", flush=True)


if __name__ == "__main__":
    main()
