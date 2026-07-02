"""A11 S4 — machine validation of the dangerous-sector reduction (Entry 2).

Validates the load-bearing identities behind the Entry-2 propositions
(A_HANDOFF §4 discipline: adversarially check every intermediate claim
before quoting a proof):

  V1  cover-boundary block form: with the sheet embedding fixed by the
      fundamental domain, ∂₂^cov = [[∂₂nc, ∂₂c],[∂₂c, ∂₂nc]] and
      ∂₂nc + ∂₂c = ∂₂^base (same for ∂₁).
  V2  half-boundary agreement on the kernel: ζ ∈ ker ∂₂ ⟹ ∂₂c ζ = ∂₂nc ζ
      (the Δ chain formula / fiber-absorption input).
  V3  Prop-2 forward: for random (ρ, y), v := τ(ρ) + ∂₂^cov(y,0) is a
      cover cycle with p(v) = ∂₂ y and sheets (ρ + ∂₂nc y, ρ + ∂₂c y).
  V4  Prop-2 backward on a real minimum: take the SAT min-weight cover
      logical v; if p(v) is a base stabilizer (dangerous), solve
      ∂₂ y = p(v), and check w := v + ∂₂^cov(y,0) is DIAGONAL with w₀ a
      base cycle (the claimed decomposition v = τ(w₀) + ∂₂(y,0)).
  V5  y-freedom absorption: replacing y by y + ζ (ζ ∈ ker ∂₂) changes
      the sheet pair by (∂₂c ζ, ∂₂c ζ) — i.e. exactly a τ-shift of ρ.

Instances: the Lean-proven Z3Z6 pair (x-cover, d = 8) and hit3's stored
form (x-cover, d = 6, safe-breaking) as a second frame.

Usage:  uv run python scripts/a11_s4_dangerous_reduction.py
"""

from __future__ import annotations

import sys
from pathlib import Path

import numpy as np

LAB_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LAB_ROOT / "src"))
sys.path.insert(0, str(LAB_ROOT / "scripts"))

from bb_lab.checks import bb_check_matrices
from bb_lab.group import AbelianGroup
from bb_lab.linalg import nullspace_f2, rank_f2
from bb_lab.poly import Poly
from bb_lab.sat_distance import x_distance

from a9_lean_target_screen import cover_group, in_rowspace, lift_poly

RNG = np.random.default_rng(11)
CHECKS: list[tuple[str, bool]] = []


def check(name: str, ok: bool) -> None:
    CHECKS.append((name, ok))
    print(f"  [{'PASS' if ok else 'FAIL'}] {name}", flush=True)


def sheet_maps(ell: int, m: int, axis: str):
    """Index maps: cover qubit index <-> (sheet, base qubit index)."""
    Gb, Gc = AbelianGroup((ell, m)), cover_group(ell, m, axis)
    nb, nc = Gb.cardinality, Gc.cardinality
    # S[s] : base cell index -> cover cell index on sheet s
    S = np.zeros((2, nb), dtype=np.int64)
    for g in Gb:
        S[0, Gb.index(g)] = Gc.index(g)
        gg = (g[0] + ell, g[1]) if axis == "x" else (g[0], g[1] + m)
        S[1, Gb.index(g)] = Gc.index(gg)
    # qubit-level (two blocks of size n_cells)
    Q = np.zeros((2, 2 * nb), dtype=np.int64)
    for blk in (0, 1):
        Q[0, blk * nb: (blk + 1) * nb] = blk * nc + S[0]
        Q[1, blk * nb: (blk + 1) * nb] = blk * nc + S[1]
    return Gb, Gc, S, Q


def run_instance(tag: str, ell: int, m: int, A_s: str, B_s: str, axis: str,
                 dcap: int) -> None:
    print(f"\n== {tag} (Z{ell}xZ{m}, axis {axis}) ==")
    Gb, Gc, S, Q = sheet_maps(ell, m, axis)
    nb, ncell = Gb.cardinality, Gc.cardinality
    A, B = Poly.from_string(A_s, Gb), Poly.from_string(B_s, Gb)
    chb = bb_check_matrices(A, B)
    chc = bb_check_matrices(lift_poly(A, Gc), lift_poly(B, Gc))
    d1b = chb.H_X.astype(np.uint8)               # base ∂1: cells x 2cells
    d2b = chb.H_Z.astype(np.uint8).T             # base ∂2: qubits(2n) x cells(n)
    d1c = chc.H_X.astype(np.uint8)
    d2c_full = chc.H_Z.astype(np.uint8).T        # cover ∂2

    # --- V1: extract nc/c parts of ∂2 by sheet classification -------------
    # column z of cover ∂2 for a sheet-0 2-cell: entries on sheet 0 -> nc,
    # sheet 1 -> c.  (2-cells of the cover = cells of Gc; sheet-0 2-cell of
    # base cell j is S[0, j].)
    d2nc = np.zeros((2 * nb, nb), dtype=np.uint8)
    d2cc = np.zeros((2 * nb, nb), dtype=np.uint8)
    inv_q = {}
    for s in (0, 1):
        for i, qi in enumerate(Q[s]):
            inv_q[qi] = (s, i)
    for j in range(nb):
        col = d2c_full[:, S[0, j]]
        for qi in np.flatnonzero(col):
            s, i = inv_q[qi]
            (d2nc if s == 0 else d2cc)[i, j] ^= 1
    check("V1a: d2nc + d2c == base d2", bool(((d2nc ^ d2cc) == d2b).all()))
    # reconstruct the full cover ∂2 from the block form and compare
    recon = np.zeros_like(d2c_full)
    for j in range(nb):
        for s in (0, 1):
            colv = np.zeros(2 * ncell, dtype=np.uint8)
            colv[Q[s]] ^= d2nc[:, j]
            colv[Q[1 - s]] ^= d2cc[:, j]
            recon[:, S[s, j]] = colv
    check("V1b: [[nc,c],[c,nc]] reconstructs cover d2", bool((recon == d2c_full).all()))

    # --- V2: kernel half-boundaries agree ---------------------------------
    ker2 = nullspace_f2(d2b)  # rows: ζ with d2 ζ = 0? careful: d2b is (2n x n);
    # nullspace_f2(M) = {z : M z = 0}; here z ranges over 2-cells ✓
    ok2 = all(
        bool((((d2nc @ z) % 2) == ((d2cc @ z) % 2)).all()) for z in (ker2 % 2)
    ) if ker2.shape[0] else True
    check(f"V2: d2c ζ == d2nc ζ on ker d2 (dim {ker2.shape[0]})", ok2)

    # --- helpers: tau, p at qubit level -----------------------------------
    def tau(u: np.ndarray) -> np.ndarray:
        v = np.zeros(4 * nb, dtype=np.uint8)  # 2*ncell = 4*nb qubits? ncell=2nb
        v = np.zeros(2 * ncell, dtype=np.uint8)
        v[Q[0]] ^= u
        v[Q[1]] ^= u
        return v

    def proj(v: np.ndarray) -> np.ndarray:
        return (v[Q[0]] ^ v[Q[1]]).astype(np.uint8)

    def d2cov_sheet0(y: np.ndarray, M: np.ndarray | None = None) -> np.ndarray:
        """∂2^cov (y, 0): the boundary of a sheet-0 2-chain y (matrix M
        defaults to the primal cover ∂2)."""
        Mm = d2c_full if M is None else M
        w = np.zeros(2 * ncell, dtype=np.uint8)
        for j in np.flatnonzero(y):
            w ^= Mm[:, S[0, j]]
        return w

    # --- V3: forward parametrization --------------------------------------
    ok3 = True
    kerX = nullspace_f2(d1b)   # base cycles
    for _ in range(50):
        rho = (kerX[RNG.integers(0, kerX.shape[0])] if kerX.shape[0] else
               np.zeros(2 * nb, np.uint8))
        # random sparse combination of cycles
        coeff = RNG.integers(0, 2, kerX.shape[0]).astype(np.uint8)
        rho = (coeff @ kerX) % 2
        y = RNG.integers(0, 2, nb).astype(np.uint8)
        v = tau(rho) ^ d2cov_sheet0(y)
        b = (d2b @ y) % 2
        ok3 &= not ((d1c @ v) % 2).any()          # cycle
        ok3 &= bool((proj(v) == b).all())          # projection
        s0, s1 = v[Q[0]], v[Q[1]]
        ok3 &= bool((s0 == (rho ^ ((d2nc @ y) % 2))).all())
        ok3 &= bool((s1 == (rho ^ ((d2cc @ y) % 2))).all())
    check("V3: τ(ρ)+∂2(y,0) is a dangerous cycle with the claimed sheets", ok3)

    # --- V5: y-freedom == fiber shift --------------------------------------
    ok5 = True
    for _ in range(20):
        y = RNG.integers(0, 2, nb).astype(np.uint8)
        if ker2.shape[0] == 0:
            break
        zeta = ker2[RNG.integers(0, ker2.shape[0])] % 2
        h_shift = (d2cc @ zeta) % 2
        v1 = d2cov_sheet0((y ^ zeta).astype(np.uint8))
        v2 = d2cov_sheet0(y) ^ tau(h_shift)
        ok5 &= bool((v1 == v2).all())
    check("V5: y -> y+ζ shifts the pair by τ(∂2c ζ) exactly", ok5)

    # --- V4: backward decomposition of the true SAT minimum ----------------
    # x_distance witnesses are X-type (ker H_Z): run the decomposition on
    # the DUAL complex (∂1 := H_Z, ∂2 := H_Xᵀ, stabilizers = rowspace H_X).
    res = x_distance(chc, weight_upper_bound=dcap)
    v = res.witness.astype(np.uint8)
    b = proj(v)
    HXb = chb.H_X.astype(np.uint8)
    d1b = chb.H_Z.astype(np.uint8)            # dual ∂1
    d1c = chc.H_Z.astype(np.uint8)
    d2b = chb.H_X.astype(np.uint8).T          # dual ∂2
    d2c_full = chc.H_X.astype(np.uint8).T
    dangerous = (not b.any()) or in_rowspace(HXb, b)
    print(f"  min-weight cover X-logical: |v| = {int(v.sum())}, "
          f"|p(v)| = {int(b.sum())}, dual-side sector = "
          f"{'dangerous' if dangerous else 'safe'}")
    if dangerous:
        # solve d2 y = b over F2 (Gaussian elimination via stacked rank)
        Mt = d2b.copy().astype(np.uint8)
        # augmented solve
        aug = np.concatenate([Mt, b[:, None]], axis=1) % 2
        # simple GF(2) elimination
        Maug = aug.copy()
        rows, cols = Maug.shape
        piv_cols, r = [], 0
        for c in range(cols - 1):
            pr = None
            for rr in range(r, rows):
                if Maug[rr, c]:
                    pr = rr
                    break
            if pr is None:
                continue
            Maug[[r, pr]] = Maug[[pr, r]]
            for rr in range(rows):
                if rr != r and Maug[rr, c]:
                    Maug[rr] ^= Maug[r]
            piv_cols.append(c)
            r += 1
        y = np.zeros(nb, dtype=np.uint8)
        solvable = True
        for rr in range(r, rows):
            if Maug[rr, :-1].any() == 0 and Maug[rr, -1]:
                solvable = False
        for i, c in enumerate(piv_cols):
            y[c] = Maug[i, -1]
        check("V4a: p(v) ∈ im ∂2 solvable", solvable and
              bool((((d2b @ y) % 2) == b).all()))
        w = v ^ d2cov_sheet0(y)
        w0, w1 = w[Q[0]], w[Q[1]]
        check("V4b: v + ∂2(y,0) is diagonal (τ-form)", bool((w0 == w1).all()))
        check("V4c: its sheet component is a base cycle",
              not ((d1b @ w0) % 2).any())
        check("V4d: τ-fiber rep is a NONTRIVIAL base logical (τ-nontriv.)",
              not in_rowspace(HXb, w0))


def main() -> None:
    run_instance("Z3Z6 doc pair", 3, 6, "x^2 + y + y^3", "1 + x + y^2", "x", 8)
    run_instance("hit3 stored", 6, 6, "y^3 + x + x^2", "y + x*y^2 + x^2", "x", 6)
    n_fail = sum(1 for _, ok in CHECKS if not ok)
    print(f"\n{len(CHECKS)} checks, {n_fail} failures")
    sys.exit(1 if n_fail else 0)


if __name__ == "__main__":
    main()
