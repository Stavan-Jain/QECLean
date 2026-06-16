"""A3 / Track 1.1 Entry 5 — discovery scan of m(b) over light base stabilizers.

Given the verified reduction (a3_mb_foundations.py): for every base stabilizer
b, the minimum weight of a nontrivial dangerous cover logical v with p(v) = b is

    |b| + 2*m(b),
    m(b) = min{ |(d2c z_b + u') off supp(b)| : u' in Z1(base), [u'] not in im(Delta) },

(cut-independent; z_b any fixed d2-preimage of b). The factor-2 lemma
    "dangerous nontrivial => |v| >= 2*d_base = 12"
is exactly:  |b| + 2*m(b) >= 12 for ALL stabilizers b.

This scan:
  S1  enumerates ALL stabilizers b with 0 < |b| <= 11 (SAT, blocking clauses);
  S2  classifies each by min-preimage face count k_min and G-orbit;
  S3  computes m(b) exactly (SAT min over punctured weight, cut 0);
      spot-checks cut-independence (j = 0..5) and translation-invariance;
  S4  verdict per b: |b| + 2*m(b) >= 12 ?  (the lemma, restricted to light b);
  S5  computes m(0) (the clean case; expect 6 = d_base);
  S6  decodes one s!=0 weight-14 minimizer and one [c]=0 weight-15 minimizer
      from the validated Entry-2 encodings into (b, m) coordinates, tying the
      old case-split numbers to the new picture.

Discovery/validation only; never load-bearing in a final analytic proof.
"""
from __future__ import annotations

import numpy as np
from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195

from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.checks import bb_check_matrices
from bb_lab.linalg import nullspace_f2, rank_f2, quotient_complement_basis
from bb_lab.sat_distance import _xor_chain

rng = np.random.default_rng(20260612)

# ---------------------------------------------------------------- build codes
Gc = ZmZn(12, 6); Ac = Poly.from_string("x^3 + y + y^2", Gc); Bc = Poly.from_string("y^3 + x + x^2", Gc)
Gb = ZmZn(6, 6);  Ab = Poly.from_string("x^3 + y + y^2", Gb); Bb = Poly.from_string("y^3 + x + x^2", Gb)
cm_c = bb_check_matrices(Ac, Bc); cm_b = bb_check_matrices(Ab, Bb)
HXc, HZc = cm_c.H_X & 1, cm_c.H_Z & 1
HXb, HZb = cm_b.H_X & 1, cm_b.H_Z & 1
nc, nb = Gc.cardinality, Gb.cardinality
N, n = 2 * nc, 2 * nb
d2b = HZb.T
d2cov = HZc.T

def base_of(g): return (g[0] % 6, g[1])

P1 = np.zeros((n, N), np.uint8); P2 = np.zeros((nb, nc), np.uint8)
for g in Gc:
    gi, bi = Gc.index(g), Gb.index(base_of(g))
    P1[bi, gi] ^= 1; P1[nb + bi, nc + gi] ^= 1
    P2[bi, gi] ^= 1
TAU1 = P1.T.copy()

def cut_mats(j: int):
    def sheet(g): return 1 if ((g[0] - j) % 12) >= 6 else 0
    row_perm = np.empty(nc, dtype=int); col_perm = np.empty(N, dtype=int)
    for g in Gc:
        gi, bi = Gc.index(g), Gb.index(base_of(g))
        row_perm[gi] = sheet(g) * nb + bi
        for blk in (0, 1):
            col_perm[blk * nc + gi] = sheet(g) * n + blk * nb + bi
    HXc_p = np.zeros_like(HXc); HXc_p[row_perm[:, None], col_perm[None, :]] = HXc
    HZc_p = np.zeros_like(HZc); HZc_p[row_perm[:, None], col_perm[None, :]] = HZc
    d1c = HXc_p[:nb, n:]
    d2c = HZc_p[:nb, n:].T
    R0 = np.zeros((n, N), np.uint8)
    for g in Gc:
        if sheet(g) == 0:
            gi, bi = Gc.index(g), Gb.index(base_of(g))
            R0[bi, gi] = 1; R0[nb + bi, nc + gi] = 1
    return d1c, d2c, R0

CUTS = [cut_mats(j) for j in range(6)]
d1c0, d2c0, R0_0 = CUTS[0]

ker_d2b = nullspace_f2(d2b)                                   # 6 x 36
Z1b = nullspace_f2(HXb)
logXb = quotient_complement_basis(HXb, nullspace_f2(HZb))
logXc = quotient_complement_basis(HXc, nullspace_f2(HZc))
imD_cls = (((d2c0 @ ker_d2b.T).T % 2) @ logXb.T) % 2
mu = nullspace_f2(imD_cls)
eta = (mu @ logXb) % 2                                        # 6 x 72

# ------------------------------------------------------------- F2 solve helper
def f2_solve(A: np.ndarray, rhs: np.ndarray) -> np.ndarray | None:
    """One solution x of A x = rhs over F2, or None."""
    A = (A & 1).astype(np.uint8); rhs = (rhs & 1).astype(np.uint8)
    m, k = A.shape
    Aug = np.concatenate([A, rhs.reshape(-1, 1)], axis=1)
    piv_row = 0; piv_cols = []
    for col in range(k):
        nz = np.flatnonzero(Aug[piv_row:, col])
        if nz.size == 0:
            continue
        r = piv_row + int(nz[0])
        if r != piv_row:
            Aug[[piv_row, r]] = Aug[[r, piv_row]]
        mask = Aug[:, col] == 1; mask[piv_row] = False
        if mask.any():
            Aug[mask] ^= Aug[piv_row]
        piv_cols.append(col); piv_row += 1
        if piv_row == m:
            break
    if Aug[piv_row:, :k].any() is False:
        pass
    for r in range(piv_row, m):
        if not Aug[r, :k].any() and Aug[r, k]:
            return None
    x = np.zeros(k, np.uint8)
    for i, col in enumerate(piv_cols):
        x[col] = Aug[i, k]
    return x

# ---------------------------------------------------- S1: enumerate light b's
print("=== S1: enumerate all stabilizers b with 0 < |b| <= 11 ===")
pool = IDPool(); cnf = CNF()
zv = [pool.id() for _ in range(nb)]
b_out = []
for q in range(n):
    o = _xor_chain((zv[f] for f in np.flatnonzero(d2b[q])), pool, cnf)
    b_out.append(o)                                            # row weight 3 => never None
cnf.append([o for o in b_out if o is not None])                # b != 0
card = CardEnc.atmost(lits=[o for o in b_out if o is not None], bound=11,
                      vpool=pool, encoding=EncType.seqcounter)
cnf.extend(card.clauses)
solver = Cadical195(bootstrap_with=cnf.clauses)
light_bs = []
while solver.solve():
    model = set(l for l in solver.get_model() if l > 0)
    b = np.array([1 if (o in model) else 0 for o in b_out], np.uint8)
    light_bs.append(b)
    solver.add_clause([-o if (o in model) else o for o in b_out])
    if len(light_bs) >= 20000:
        print("  !! enumeration cap hit"); break
solver.delete()
print(f"  found {len(light_bs)} stabilizers with weight in 1..11")

# ------------------------------------------- S2: classify (k_min, weight, s_j)
def min_preimage(b):
    z0 = f2_solve(d2b, b)
    assert z0 is not None and not ((d2b @ z0) % 2 ^ b).any()
    best, bz = None, None
    for mask in range(1 << ker_d2b.shape[0]):
        z = z0.copy()
        for i in range(ker_d2b.shape[0]):
            if (mask >> i) & 1:
                z ^= ker_d2b[i]
        w = int(z.sum())
        if best is None or w < best:
            best, bz = w, z
    return best, bz

fam: dict[tuple[int, int], list[int]] = {}
info = []
for idx, b in enumerate(light_bs):
    k_min, z_b = min_preimage(b)
    sflags = tuple(int(((CUTS[j][0] @ b) % 2).any()) for j in range(6))
    info.append({"b": b, "w": int(b.sum()), "k": k_min, "z": z_b, "s": sflags})
    fam.setdefault((int(b.sum()), k_min), []).append(idx)
print("  families (|b|, k_min) -> count:")
for key in sorted(fam):
    print(f"    {key}: {len(fam[key])}")

# ---------------------------------------------------------- S3: m(b) via SAT
def m_of(b: np.ndarray, z_b: np.ndarray, j: int = 0, cap: int = 8) -> int | None:
    """Exact m_j(b); None means > cap."""
    d1c, d2c, _ = CUTS[j]
    shift = (d2c @ z_b) % 2
    off = np.flatnonzero(b == 0)
    for w in range(cap + 1):
        pool = IDPool(); cnf = CNF()
        uv = [pool.id() for _ in range(n)]
        for r in HXb:                                          # cycle
            o = _xor_chain((uv[i] for i in np.flatnonzero(r)), pool, cnf)
            if o is not None:
                cnf.append([-o])
        outs = []                                              # class not in imD
        for r in eta:
            o = _xor_chain((uv[i] for i in np.flatnonzero(r)), pool, cnf)
            if o is not None:
                outs.append(o)
        cnf.append(outs)
        lits = [(uv[q] if shift[q] == 0 else -uv[q]) for q in off]
        card = CardEnc.atmost(lits=lits, bound=w, vpool=pool, encoding=EncType.seqcounter)
        cnf.extend(card.clauses)
        s = Cadical195(bootstrap_with=cnf.clauses)
        sat = s.solve(); s.delete()
        if sat:
            return w
    return None

print("\n=== S5: clean case m(0) (expect 6 = d_base) ===")
m0 = m_of(np.zeros(n, np.uint8), np.zeros(nb, np.uint8))
print(f"  m(0) = {m0}  ->  |b| + 2 m = {2 * (m0 if m0 is not None else 99)}")

print("\n=== S3/S4: m(b) over all light b (cut 0), verdict vs >= 12 ===")
worst = {}
viol = []
for idx, rec in enumerate(info):
    m = m_of(rec["b"], rec["z"])
    rec["m"] = m
    val = rec["w"] + 2 * (m if m is not None else 99)
    key = (rec["w"], rec["k"])
    if key not in worst or val < worst[key][0]:
        worst[key] = (val, idx)
    if val < 12:
        viol.append(idx)
    if (idx + 1) % 50 == 0:
        print(f"  ... {idx + 1}/{len(info)} scanned")
print("  family (|b|, k_min):  worst |b|+2m(b)   [m exact, '>8' if capped]")
for key in sorted(worst):
    val, idx = worst[key]
    mtxt = info[idx]["m"] if info[idx]["m"] is not None else ">8"
    print(f"    {key}: worst value {val}  (m = {mtxt})")
print(f"  VIOLATIONS of |b|+2m >= 12: {len(viol)}")
for idx in viol[:10]:
    print(f"    b idx {idx}: w={info[idx]['w']} k={info[idx]['k']} m={info[idx]['m']}")

# cut-independence + translation-invariance spot checks
print("\n=== S3b: cut-independence + translation-invariance spot checks ===")
sample = list(range(min(3, len(info)))) + list(rng.integers(0, len(info), 3))
ok_cut = True
for idx in sample:
    ms = [m_of(info[idx]["b"], info[idx]["z"], j=j, cap=8) for j in range(6)]
    ok_cut &= len(set(ms)) == 1
    print(f"  b idx {idx} (w={info[idx]['w']}, k={info[idx]['k']}): m_j = {ms}")
print(f"  cut-independent on sample: {ok_cut}")

def translate_vec(b, dx, dy):
    out = np.zeros_like(b)
    for g in Gb:
        gi = Gb.index(g); ti = Gb.index(((g[0] + dx) % 6, (g[1] + dy) % 6))
        out[ti] = b[gi]; out[nb + ti] = b[nb + gi]
    return out

ok_tr = True
for idx in sample[:3]:
    b2 = translate_vec(info[idx]["b"], 1, 2)
    z2 = f2_solve(d2b, b2)
    m2 = m_of(b2, z2)
    ok_tr &= (m2 == info[idx]["m"])
print(f"  translation-invariant on sample: {ok_tr}")

# ----------------------------------------- S6: decode old-SAT minimizers
print("\n=== S6: decode Entry-2 minimizers into (b, m) coordinates ===")
D = np.array([((P1.T @ (g & 1)) % 2) for g in logXb], dtype=np.uint8)
S_rows = (d1c0 @ P1) % 2

def find_witness(weight, mode):
    pool = IDPool(); qv = [pool.id() for _ in range(N)]; cnf = CNF()
    def parity(row):
        return _xor_chain((qv[i] for i in np.flatnonzero(row)), pool, cnf)
    for r in HXc:
        o = parity(r)
        if o is not None: cnf.append([-o])
    for r in D:
        o = parity(r)
        if o is not None: cnf.append([-o])
    outs = [parity(L & 1) for L in logXc]
    cnf.append([o for o in outs if o is not None])
    if mode == "s_nonzero":
        outs = [parity(r) for r in S_rows]
        cnf.append([o for o in outs if o is not None])
    elif mode == "c_zero":
        for r in S_rows:
            o = parity(r)
            if o is not None: cnf.append([-o])
        for g in logXb:
            o = parity((R0_0.T @ (g & 1)) % 2)
            if o is not None: cnf.append([-o])
    card = CardEnc.atmost(lits=qv, bound=weight, vpool=pool, encoding=EncType.seqcounter)
    cnf.extend(card.clauses)
    s = Cadical195(bootstrap_with=cnf.clauses)
    sat = s.solve()
    v = None
    if sat:
        model = set(l for l in s.get_model() if l > 0)
        v = np.array([1 if q in model else 0 for q in qv], np.uint8)
    s.delete()
    return v

for mode, wcap in (("s_nonzero", 14), ("c_zero", 15)):
    v = find_witness(wcap, mode)
    if v is None:
        print(f"  {mode} @ w<={wcap}: UNSAT (unexpected!)"); continue
    b = (P1 @ v) % 2
    z_b = f2_solve(d2b, b)
    k_min, _ = min_preimage(b)
    v0 = (R0_0 @ v) % 2
    offw = int(v0[b == 0].sum())
    sig = (eta @ ((v0 + (d2c0 @ z_b)) % 2)) % 2
    sj = [int(((CUTS[j][0] @ b) % 2).any()) for j in range(6)]
    print(f"  {mode} witness: |v|={int(v.sum())}, |b|={int(b.sum())}, k_min={k_min}, "
          f"|v0 off b|={offw}, eta-sig nonzero={bool(sig.any())}, s_j flags={sj}")
    if int(b.sum()) <= 11:
        midx = next((i for i, r in enumerate(info) if np.array_equal(r["b"], b)), None)
        print(f"    b is light; in scan: {midx is not None}"
              + (f", scanned m(b) = {info[midx]['m']}" if midx is not None else ""))

print("\nDone.")
