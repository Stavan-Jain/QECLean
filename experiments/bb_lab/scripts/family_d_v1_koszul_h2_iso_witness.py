"""§6m witness — H_0(K) and H_2(K) are F_2[G]-isomorphic for gross, but
their minimum Hamming weights differ by 32×.

This script is the **computational anchor** for HANDOFF.md §6m. It
demonstrates rigorously that minimum Hamming weight is NOT an
F_2[G]-module-isomorphism-class invariant by:

1. Building both H_0 = F_2[G]/(A,B) and H_2 = Ann(A) ∩ Ann(B) as
   explicit F_2[G]-modules for the gross polynomials.
2. Computing the matrices of the multiplication-by-x and
   multiplication-by-y actions on each module.
3. Searching the F_2-vector space of intertwiners (linear maps
   U: H_0 → H_2 commuting with both x-action and y-action) for an
   invertible element — its existence is the iso-witness.
4. Reporting the minimum Hamming weights of both modules in their
   canonical embeddings into F_2[G] (resp. F_2[G]^1 embedded in
   F_2[G] via the F_2-linear map from H_2_basis).

The gap min_wt(H_0) = 1 vs min_wt(H_2) = 32 over the SAME F_2[G]-
module class is the empirical anchor for the §6m obstruction:

> Min Hamming weight depends on the embedding ι: M ↪ F_2[G]^k, not
> on the abstract module class [M].

This implies no F_2[G]-module-natural numerical invariant ψ([M(A,B)])
can tightly lower-bound d_X(A, B), because ψ is constant on the
iso-class while min weight varies.

Usage:
    uv run python scripts/family_d_v1_koszul_h2_iso_witness.py
"""

from __future__ import annotations

import numpy as np

from bb_lab.checks import circulant
from bb_lab.group import ZmZn
from bb_lab.linalg import nullspace_f2, rank_f2
from bb_lab.poly import Poly


def _shift_matrix(ell: int, m: int, dx: int, dy: int) -> np.ndarray:
    """Permutation matrix for the action of (dx, dy) ∈ Z_ell × Z_m on F_2^{ell·m}.

    With the row-major basis e_{(i,j)} = e[i*m + j], the action
    (dx, dy)·e_{(i,j)} = e_{((i+dx) mod ell, (j+dy) mod m)} translates
    to matrix entries M[tgt, src] = 1.
    """
    n = ell * m
    M = np.zeros((n, n), dtype=np.uint8)
    for i in range(ell):
        for j in range(m):
            src = i * m + j
            tgt = ((i + dx) % ell) * m + ((j + dy) % m)
            M[tgt, src] = 1
    return M


def _rref(M: np.ndarray) -> tuple[np.ndarray, list[int]]:
    """Reduced row-echelon form over F_2; returns (rref, pivot_cols)."""
    M = M.copy().astype(np.uint8)
    rows, cols = M.shape
    pivot_row = 0
    pivot_cols: list[int] = []
    for c in range(cols):
        if pivot_row >= rows:
            break
        pivots = np.where(M[pivot_row:, c] == 1)[0]
        if len(pivots) == 0:
            continue
        p = pivots[0] + pivot_row
        if p != pivot_row:
            M[[pivot_row, p]] = M[[p, pivot_row]]
        for r in range(rows):
            if r != pivot_row and M[r, c] == 1:
                M[r] = (M[r] ^ M[pivot_row]) & 1
        pivot_cols.append(c)
        pivot_row += 1
    return M, pivot_cols


def _solve_f2(A: np.ndarray, b: np.ndarray) -> np.ndarray | None:
    """Return some F_2-solution to Ax = b, or None if inconsistent."""
    aug = np.concatenate([A, b[:, None]], axis=1)
    M, pivots = _rref(aug)
    rows = M.shape[0]
    # Inconsistency check.
    for r in range(len(pivots), rows):
        if M[r, -1] == 1:
            return None
    x = np.zeros(A.shape[1], dtype=np.uint8)
    for i, c in enumerate(pivots):
        if c < A.shape[1]:
            x[c] = M[i, -1]
    return x


def _project_to_cokernel(
    v: np.ndarray, H_X: np.ndarray, coset_proj: np.ndarray
) -> np.ndarray:
    """Express v ∈ F_2^n as (image part) + (cokernel part) and return
    the cokernel part's coordinates in the basis from `coset_proj`.

    `H_X` has columns spanning the image (n × 2n stacked from M_A | M_B).
    `coset_proj` has 6 columns selected from the identity, spanning a
    complement of the image in F_2^n.
    """
    A_full = np.concatenate([H_X, coset_proj], axis=1)
    x = _solve_f2(A_full, v)
    if x is None:
        raise RuntimeError(
            "H_X columns + coset_proj columns failed to span F_2^n"
        )
    n_H_X_cols = H_X.shape[1]
    return x[n_H_X_cols:]


def _project_to_H2(v: np.ndarray, H2_basis: np.ndarray) -> np.ndarray | None:
    """If v is in the F_2-span of H2_basis rows, return its coordinates;
    otherwise None."""
    return _solve_f2(H2_basis.T, v)


def _kron_f2(A: np.ndarray, B: np.ndarray) -> np.ndarray:
    return np.kron(A, B).astype(np.uint8) % 2


def _intertwiner_constraint(M_left: np.ndarray, M_right: np.ndarray) -> np.ndarray:
    """Linearize `M_left @ U = U @ M_right` as a homogeneous F_2-system
    on vec(U) (row-major). Returns the constraint matrix.

    With row-major vec (vec(U)[i*k+j] = U[i, j]), we have
        vec(M_left @ U) = (M_left ⊗ I_k) · vec(U)
        vec(U @ M_right) = (I_k ⊗ M_right.T) · vec(U)
    so the homogeneous constraint matrix is
        (M_left ⊗ I_k) ⊕ (I_k ⊗ M_right.T)
    (mod 2). For 6×6 matrices, vec(U) has length 36 and the returned
    matrix is 36×36.
    """
    k = M_left.shape[0]
    eye = np.eye(k, dtype=np.uint8)
    return (_kron_f2(M_left, eye) ^ _kron_f2(eye, M_right.T)) % 2


def main() -> None:
    print("=" * 78)
    print("§6m WITNESS — H_0(K_gross) ≅ H_2(K_gross) as F_2[G]-modules,")
    print("              but min_wt(H_0) = 1 and min_wt(H_2) = 32.")
    print("=" * 78)

    # Gross polynomials.
    ell, m = 12, 6
    G = ZmZn(ell, m)
    A = Poly.from_string("x^3 + y + y^2", G)
    B = Poly.from_string("y^3 + x + x^2", G)
    M_A = circulant(A)
    M_B = circulant(B)
    n = G.cardinality
    assert n == 72

    H_X = np.concatenate([M_A, M_B], axis=1)  # n × 2n
    H_X_rank = rank_f2(H_X)
    dim_H_0 = n - H_X_rank
    print(f"\n|G| = {n}")
    print(f"rank H_X = {H_X_rank}, dim H_0 = {dim_H_0}")

    # --- Build H_0 -------------------------------------------------------
    # Pick 6 basis indices for H_0 = F_2^n / image(H_X).
    coset_indices: list[int] = []
    current = H_X.copy()
    for i in range(n):
        e_i = np.zeros(n, dtype=np.uint8)
        e_i[i] = 1
        aug = np.concatenate([current, e_i[:, None]], axis=1)
        if rank_f2(aug) > rank_f2(current):
            coset_indices.append(i)
            current = aug
        if len(coset_indices) == dim_H_0:
            break
    assert len(coset_indices) == dim_H_0
    print(f"H_0 basis coset indices: {coset_indices}")
    coset_proj = np.eye(n, dtype=np.uint8)[:, coset_indices]

    # --- Build H_2 -------------------------------------------------------
    H2_basis = nullspace_f2(np.concatenate([M_A, M_B], axis=0))
    dim_H_2 = H2_basis.shape[0]
    print(f"dim H_2 = {dim_H_2}")
    assert dim_H_2 == dim_H_0, "dim H_0 and dim H_2 must match for the iso"

    # --- Action matrices -------------------------------------------------
    M_x = _shift_matrix(ell, m, 1, 0)
    M_y = _shift_matrix(ell, m, 0, 1)

    # x-action on H_0 (6×6 matrix in the coset basis):
    M_x_H0 = np.zeros((dim_H_0, dim_H_0), dtype=np.uint8)
    for j, idx in enumerate(coset_indices):
        e = np.zeros(n, dtype=np.uint8)
        e[idx] = 1
        xe = (M_x @ e) % 2
        coords = _project_to_cokernel(xe, H_X, coset_proj)
        M_x_H0[:, j] = coords
    M_y_H0 = np.zeros((dim_H_0, dim_H_0), dtype=np.uint8)
    for j, idx in enumerate(coset_indices):
        e = np.zeros(n, dtype=np.uint8)
        e[idx] = 1
        ye = (M_y @ e) % 2
        coords = _project_to_cokernel(ye, H_X, coset_proj)
        M_y_H0[:, j] = coords

    # x-action on H_2:
    M_x_H2 = np.zeros((dim_H_2, dim_H_2), dtype=np.uint8)
    M_y_H2 = np.zeros((dim_H_2, dim_H_2), dtype=np.uint8)
    for j in range(dim_H_2):
        v = H2_basis[j]
        xv = (M_x @ v) % 2
        coords = _project_to_H2(xv, H2_basis)
        assert coords is not None, "H_2 not closed under x-action"
        M_x_H2[:, j] = coords
        yv = (M_y @ v) % 2
        coords = _project_to_H2(yv, H2_basis)
        assert coords is not None, "H_2 not closed under y-action"
        M_y_H2[:, j] = coords

    print(f"\nM_x|_{{H_0}}:\n{M_x_H0}")
    print(f"\nM_x|_{{H_2}}:\n{M_x_H2}")

    # --- Iso witness: find invertible U with U · M_x_H0 = M_x_H2 · U ----
    # Linearize the constraint and find the F_2-null-space.
    C_x = _intertwiner_constraint(M_x_H2, M_x_H0)
    C_y = _intertwiner_constraint(M_y_H2, M_y_H0)
    C = np.concatenate([C_x, C_y], axis=0)
    null = nullspace_f2(C)
    print(f"\nIntertwiner space (rows commuting with both x and y actions): dim = {null.shape[0]}")

    # Enumerate non-trivial F_2-combinations; check invertibility.
    invertible_witnesses = 0
    first_witness: np.ndarray | None = None
    max_search = min(1 << null.shape[0], 1 << 12)
    for mask in range(1, max_search):
        U_vec = np.zeros(null.shape[1], dtype=np.uint8)
        for i in range(null.shape[0]):
            if (mask >> i) & 1:
                U_vec = (U_vec ^ null[i]) % 2
        U_mat = U_vec.reshape(dim_H_0, dim_H_0)
        if rank_f2(U_mat) == dim_H_0:
            invertible_witnesses += 1
            if first_witness is None:
                first_witness = U_mat.copy()

    assert invertible_witnesses > 0, (
        "FAILED: no invertible intertwiner found; H_0 and H_2 might not "
        "be F_2[G]-isomorphic. The Frobenius duality argument should "
        "give one in principle — investigate."
    )
    print(f"Invertible intertwiners found: {invertible_witnesses}")
    print(f"\nExplicit witness U (an invertible intertwiner):\n{first_witness}")

    # Sanity-check the witness commutes.
    assert first_witness is not None
    lhs_x = (first_witness @ M_x_H0) % 2
    rhs_x = (M_x_H2 @ first_witness) % 2
    lhs_y = (first_witness @ M_y_H0) % 2
    rhs_y = (M_y_H2 @ first_witness) % 2
    assert np.array_equal(lhs_x, rhs_x), "x-intertwine check failed"
    assert np.array_equal(lhs_y, rhs_y), "y-intertwine check failed"

    # --- Min weights ----------------------------------------------------
    # min_wt(H_0): pick e_(0,0) and check it's not in image(H_X).
    e_0 = np.zeros(n, dtype=np.uint8)
    e_0[0] = 1
    aug = np.concatenate([H_X, e_0[:, None]], axis=1)
    e_0_in_image = rank_f2(aug) == rank_f2(H_X)
    min_wt_H_0 = 2 if e_0_in_image else 1

    # min_wt(H_2): brute-force enumerate non-zero F_2-combinations.
    min_wt_H_2 = n + 1
    for mask in range(1, 1 << dim_H_2):
        v = np.zeros(n, dtype=np.uint8)
        for i in range(dim_H_2):
            if (mask >> i) & 1:
                v = (v ^ H2_basis[i]) % 2
        w = int(v.sum())
        if 0 < w < min_wt_H_2:
            min_wt_H_2 = w

    print()
    print("=" * 78)
    print("WITNESS RESULTS")
    print("=" * 78)
    print(f"H_0 ≅ H_2 as F_2[G]-modules:  YES (explicit invertible "
          f"intertwiner found)")
    print(f"min_wt(H_0) (canonical embedding F_2[G]/(A,B) ⊂ F_2[G]):  "
          f"{min_wt_H_0}")
    print(f"min_wt(H_2) (canonical embedding Ann(A) ∩ Ann(B) ⊂ F_2[G]):  "
          f"{min_wt_H_2}")
    print(f"Ratio min_wt(H_2) / min_wt(H_0):  {min_wt_H_2}×")
    print()
    print("CONCLUSION: F_2[G]-module isomorphism does NOT preserve min")
    print("Hamming weight. This is the structural witness for HANDOFF.md")
    print("§6m: any function ψ([M]) that depends only on the F_2[G]-")
    print("module isomorphism class of a construction M(A, B) cannot")
    print("tightly lower-bound d_X(A, B).")


if __name__ == "__main__":
    main()
