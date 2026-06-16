"""A1 Tier-1.4 substrate: the four terms of the Eberhardt-Steffan
fundamental exact sequence (arXiv:2407.03973 Thm 2.3) for gross.

ES Theorem 2.3 (verbatim, from notes/A1_literature_L3.md):

  0 -> ann(cd)/M
       --(alpha)--> ann(c)/ann(c)(d) (+) ann(d)/(c)ann(d)
       --(beta)-->  H = Z/B
       --(gamma)--> (c) ∩ (d) / (cd)
       -> 0

  where  Z = {(f,g) in R_h (+) R_v | c f = d g},  B = {(d r, c r) | r in R},
         H = Z/B,  and
         M = { r in ann(cd) | exists f in ann(c), g in ann(d)
                              with  r d = f d  and  r c = g c }.
  The image of beta is the pure part H_h + H_v ⊂ H.

R = F_2[Z_12 x Z_6] (dim 72). c = grossA = x^3+y+y^2, d = grossB = y^3+x+x^2.
Multiplication operators are the circulants M_c, M_d, M_cd (= M_c M_d).
All terms are F_2 subquotients computed by rank/nullspace.

Sign conventions / identifications used:
  - ann(x)   = ker M_x                              (left = right, R commutative)
  - (x)      = principal ideal = im M_x = colspace(M_x)
  - x * S    for a subspace S = { M_x s : s in S }  = M_x applied to a basis of S
  - ann(c)(d) means the ideal product (ann c)·(d) = d·ann(c) = M_d[ann(c)]
        (ES writes ann(c)(d); since ann(c) is an ideal and (d)=Rd, the product
         ideal is d·ann(c). Reading confirmed against the alpha map [r]->([dr],[cr])
         landing in these quotients, i.e. the relation that is killed is exactly
         multiplication by d on ann(c)-side and by c on ann(d)-side.)
  - (c)ann(d) = c·ann(d) = M_c[ann(d)]

Self-checks:
  * H = Z/B must have dim k = 12 (Bravyi).
  * Exactness => alternating sum of the four term-dims, with H, is zero:
        dim(ann cd /M) - [dim(annc/annc d) + dim(annd/c annd)]
        + dim H - dim((c)∩(d)/(cd)) = 0.
    Equivalently dim H = (T1 + T2) - T4 + T3 where
        T1=annc/annc(d), T2=annd/(c)annd, T3=(c)∩(d)/(cd), T4=ann(cd)/M.
  * image(beta) = H_h + H_v should equal T1 + T2 - T4 (= rank of beta)
    and must match the independently-computed dim(H_h+H_v)=6 from
    scripts/a1_es_purity_check.py.
"""

import numpy as np

from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.checks import circulant
from bb_lab.linalg import rank_f2, nullspace_f2


def col_space_basis(M):
    """Basis (as columns, returned as rows) of the F_2 column space of M."""
    # column space of M = row space of M.T
    R, piv = _rref(M.T)
    return R[: len(piv)].copy()  # rows = basis vectors (length = M.shape[0])


def _rref(M):
    from bb_lab.linalg import rref_f2
    return rref_f2(M)


def apply_op_to_subspace(Op, basis_rows):
    """Given subspace S = rowspan(basis_rows) (vectors length n),
    return basis (rows) of Op[S] = { Op @ v : v in S }."""
    if basis_rows.shape[0] == 0:
        return np.zeros((0, Op.shape[0]), dtype=np.uint8)
    # columns Op @ v_i  -> stack as rows of (Op @ basis_rows.T).T
    img = (Op @ basis_rows.T % 2).T.astype(np.uint8)
    R, piv = _rref(img)
    return R[: len(piv)].copy()


def dim_rowspan(rows):
    if rows.shape[0] == 0:
        return 0
    return rank_f2(rows)


def quotient_dim(big_rows, sub_rows):
    """dim( rowspan(big) / rowspan(sub) ), assuming sub ⊆ big."""
    d_big = dim_rowspan(big_rows)
    if sub_rows.shape[0] == 0:
        return d_big
    combined = np.concatenate([big_rows, sub_rows], axis=0)
    # sub must be contained; sanity check dim(big+sub)==dim(big)
    d_union = dim_rowspan(combined)
    assert d_union == d_big, (d_union, d_big, "sub not contained in big")
    d_sub = dim_rowspan(sub_rows)
    return d_big - d_sub


def intersect_rowspans(A_rows, B_rows, n):
    """Basis (rows) of rowspan(A) ∩ rowspan(B), both living in F_2^n.
    Zassenhaus method."""
    a = A_rows.shape[0]
    b = B_rows.shape[0]
    if a == 0 or b == 0:
        return np.zeros((0, n), dtype=np.uint8)
    # Build [[A | A],[B | 0]] and row-reduce; rows with zero left half
    # have their right half spanning the intersection.
    top = np.concatenate([A_rows, A_rows], axis=1).astype(np.uint8)
    bot = np.concatenate([B_rows, np.zeros((b, n), dtype=np.uint8)], axis=1)
    M = np.concatenate([top, bot], axis=0)
    R, piv = _rref(M)
    inter = [R[r, n:].copy() for r in range(R.shape[0])
             if not R[r, :n].any() and R[r, n:].any()]
    if not inter:
        return np.zeros((0, n), dtype=np.uint8)
    return np.stack(inter).astype(np.uint8)


def main():
    G = ZmZn(12, 6)
    n = G.cardinality  # 72
    c = Poly.from_string("x^3 + y + y^2", G)  # grossA
    d = Poly.from_string("y^3 + x + x^2", G)  # grossB

    Mc = circulant(c).astype(np.uint8)        # multiplication by c
    Md = circulant(d).astype(np.uint8)        # multiplication by d
    Mcd = (Mc @ Md % 2).astype(np.uint8)      # multiplication by c*d

    # Annihilators (kernels of multiplication operators).
    annc = nullspace_f2(Mc)   # rows = basis, length n
    annd = nullspace_f2(Md)
    anncd = nullspace_f2(Mcd)

    print(f"dim R              = {n}")
    print(f"dim ann(c)         = {dim_rowspan(annc)}")
    print(f"dim ann(d)         = {dim_rowspan(annd)}")
    print(f"dim ann(cd)        = {dim_rowspan(anncd)}")
    print(f"rank M_c           = {rank_f2(Mc)}  (dim (c) = im M_c)")
    print(f"rank M_d           = {rank_f2(Md)}  (dim (d) = im M_d)")
    print(f"rank M_cd          = {rank_f2(Mcd)} (dim (cd) = im M_cd)")
    print()

    # ---- Term 1: ann(c) / ann(c)(d) = ann(c) / d*ann(c) ----------------
    annc_d = apply_op_to_subspace(Md, annc)   # d * ann(c)
    T1 = quotient_dim(annc, annc_d)
    print(f"T1 = dim ann(c)/ann(c)(d)  = {T1}   "
          f"(dim ann(c)={dim_rowspan(annc)}, dim d*ann(c)={dim_rowspan(annc_d)})")

    # ---- Term 2: ann(d) / (c)ann(d) = ann(d) / c*ann(d) ----------------
    annd_c = apply_op_to_subspace(Mc, annd)   # c * ann(d)
    T2 = quotient_dim(annd, annd_c)
    print(f"T2 = dim ann(d)/(c)ann(d)  = {T2}   "
          f"(dim ann(d)={dim_rowspan(annd)}, dim c*ann(d)={dim_rowspan(annd_c)})")

    # ---- Term 3: ((c) ∩ (d)) / (cd) -----------------------------------
    imc = col_space_basis(Mc)   # ideal (c)
    imd = col_space_basis(Md)
    imcd = col_space_basis(Mcd)  # ideal (cd) ⊆ (c) ∩ (d)
    inter = intersect_rowspans(imc, imd, n)
    T3 = quotient_dim(inter, imcd)
    print(f"T3 = dim ((c)∩(d))/(cd)    = {T3}   "
          f"(dim (c)∩(d)={dim_rowspan(inter)}, dim (cd)={dim_rowspan(imcd)})")

    # ---- Term 4: ann(cd) / M ------------------------------------------
    # M = { r in ann(cd) | exists f in ann(c), g in ann(d): rd=fd and rc=gc }.
    # rd = fd  <=>  (r-f)d = 0  <=>  r - f in ann(d)  <=>  r in f + ann(d) ⊆ ann(c)+ann(d) (since f in ann(c))
    #   So "exists f in ann(c) with rd=fd"  <=>  r in ann(c) + ann(d).
    #   (rd = fd means r ≡ f mod ann(d); pick f to be the ann(c)-part. Conversely
    #    if r = f + e with f in ann(c), e in ann(d), then rd = fd + ed = fd.)
    # rc = gc  <=>  r - g in ann(c)  <=>  r in g + ann(c) ⊆ ann(d)+ann(c).
    #   So "exists g in ann(d) with rc=gc"  <=>  r in ann(d) + ann(c).
    # Both conditions are the SAME subspace ann(c)+ann(d). Hence
    #   M = ann(cd) ∩ (ann(c) + ann(d)).
    # We verify ann(c)+ann(d) ⊆ ann(cd) (true: c,d commute so cd kills both),
    # which makes M = ann(c) + ann(d) exactly.
    sum_cd = np.concatenate([annc, annd], axis=0)
    # check containment in ann(cd)
    chk = (Mcd @ sum_cd.T % 2)
    assert not chk.any(), "ann(c)+ann(d) not killed by cd (commutativity broken?)"
    M_sub = sum_cd  # = ann(c)+ann(d), already ⊆ ann(cd)
    T4 = quotient_dim(anncd, M_sub)
    print(f"T4 = dim ann(cd)/M         = {T4}   "
          f"(dim ann(cd)={dim_rowspan(anncd)}, dim M=ann(c)+ann(d)={dim_rowspan(M_sub)})")
    print()

    # ---- self-checks ---------------------------------------------------
    # H = Z/B.  Build Z = {(f,g): c f = d g} = ker[ Mc | Md ]  (2n-dim domain)
    HX = np.concatenate([Mc, Md], axis=1) % 2     # n x 2n
    Z = nullspace_f2(HX)                          # basis of Z (length 2n)
    # B = {(d r, c r)} = colspace of [[Md],[Mc]] (2n x n) -> image rows
    Bgen = np.concatenate([Md, Mc], axis=0)       # 2n x n; columns are (dr,cr)
    Bspan = col_space_basis(Bgen)                 # rows length 2n
    dimH = quotient_dim(Z, Bspan)
    print(f"dim H = dim Z/B            = {dimH}   (should be k=12)")

    es_alt = (T1 + T2) - T4 + T3
    print(f"ES identity check: (T1+T2) - T4 + T3 = {es_alt}   (should equal dim H = {dimH})")
    print(f"  => exact-sequence alternating sum: "
          f"{'OK' if es_alt == dimH else 'MISMATCH'}")

    # image of beta = pure part H_h + H_v.  rank(beta) = (T1+T2) - rank(alpha)
    # rank(alpha) = dim(source ann(cd)/M) = T4 (alpha injective by exactness at first node).
    pure_dim = (T1 + T2) - T4
    print(f"dim image(beta) = (T1+T2) - T4 = {pure_dim}   "
          f"(= dim pure part H_h+H_v; purity script reports 6)")
    print(f"dim non-pure part = T3 (= coker beta) = {T3}")
    print(f"  pure + non-pure = {pure_dim + T3}  (should = dim H = {dimH})")


if __name__ == "__main__":
    main()
