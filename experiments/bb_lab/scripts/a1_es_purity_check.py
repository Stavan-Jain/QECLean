"""A1 gap-closer (b): is [[72,12,6]] 'pure' in the Eberhardt-Steffan sense?

ES arXiv:2407.03973 Definition 2.2: a logical class h in H = ker H_X / im H_Z^T
is horizontally pure if h = [(f,0)] (with A f = 0), vertically pure if
h = [(0,g)] (with B g = 0). H is *pure* if H = H_h + H_v.

ES Table 1 has no [[72,12,6]] row (gross at (6,12) is marked not pure /
not principal / not symmetric). Since l = m = 6 is even, ES Corollary 4.4
(l, m odd => pure & principal) does not apply, so we compute purity directly:

  dim(H_h + H_v) over F2 vs k = 12.

Also run the same check for the other chain levels for completeness.
"""

import numpy as np

from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.checks import bb_check_matrices, circulant
from bb_lab.codeparams import code_params
from bb_lab.linalg import nullspace_f2, rank_f2

CHAIN = [
    ("[[144,12,12]] gross", "x^3 + y + y^2", "y^3 + x + x^2", (12, 6)),
    ("[[72,12,6]]",         "x^3 + y + y^2", "y^3 + x + x^2", (6, 6)),
    ("[[36,8,4]]",          "1 + y + y^2",   "y^3 + x + x^2", (3, 6)),
    ("[[18,8,2]]",          "1 + y + y^2",   "1 + x + x^2",   (3, 3)),
]

for name, a_s, b_s, (l, m) in CHAIN:
    G = ZmZn(l, m)
    A = Poly.from_string(a_s, G)
    B = Poly.from_string(b_s, G)
    cm = bb_check_matrices(A, B)
    k = code_params(cm).k
    n2 = G.cardinality  # lm
    MA = circulant(A)   # lm x lm matrix of multiplication by A
    MB = circulant(B)

    # Z-logical space: ker H_X = {(f,g): MA f + MB g = 0}, mod im H_Z^T.
    HX = np.concatenate([MA, MB], axis=1) % 2          # lm x 2lm
    HZT = np.concatenate([MB, MA], axis=0) % 2         # 2lm x lm (columns span im)

    # Horizontally pure candidates: (f, 0), f in ker MA. Vertically: (0, g), g in ker MB.
    kerA = nullspace_f2(MA)   # rows = basis (shape dimker x lm)
    kerB = nullspace_f2(MB)
    horiz = np.concatenate([kerA, np.zeros_like(kerA)], axis=1)  # . x 2lm
    vert = np.concatenate([np.zeros_like(kerB), kerB], axis=1)

    # dim of (H_h + H_v) inside H = ker HX / im HZT:
    stab = HZT.T  # rows span im H_Z^T (lm x 2lm)
    r_stab = rank_f2(stab)
    pure_plus_stab = np.concatenate([stab, horiz, vert], axis=0)
    dim_pure = rank_f2(pure_plus_stab) - r_stab

    # sanity: full logical dim
    kerHX = nullspace_f2(HX)  # rows = basis of ker H_X
    dim_H = rank_f2(np.concatenate([stab, kerHX], axis=0)) - r_stab
    assert dim_H == k, (dim_H, k)

    print(f"{name:22s} (Z{l}xZ{m}): k={k}, dim(H_h+H_v)={dim_pure}  "
          f"PURE: {dim_pure == k}")
