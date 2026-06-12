"""A3 / Track 1.1 Entry 5/6 — structural facts feeding the analytic m(b) ladder.

The reduction (a3_mb_foundations.py + a3_mb_scan.py) needs, for an analytic
proof of |b| + 2 m(b) >= 12 over light stabilizers b, a small set of
structural facts about the BASE code [[72,12,6]] only. This script computes
each one exactly and states the analytic claim it instantiates.

  T1  column autocorrelation: for delta != 0, the overlap of two stabilizer
      hexagons at shift delta is ov(delta) = |A n A.delta| + |B n B.delta|.
      Claim: ov <= 1, with ov = 1 exactly on a 12-element set D
      (x-degrees of A.Abar and B.Bbar are disjoint). Consequences:
        - pairs of faces give |b| = 12 - 2 ov in {10, 12};
        - k faces, pairwise-overlap-only cancellation: |b| >= 6k - 2 e(S)
          where e(S) = overlap-graph edges (mod higher-multiplicity care).
  T2  clique structure of the overlap Cayley graph Cay(G, D): max clique,
      triangle count -- feeds the k >= 3 exclusion (Turan-type counting).
  T3  local cycle spaces (the rung facts):
        - rank of HXb on a single hexagon's 6 columns (expect 5: cycle
          space inside a hexagon = {0, b});
        - rank on the 11-qubit union of an overlapping pair (expect 9:
          cycle space = {0, col g, col h, b} -- all stabilizers);
        - hexagon + 2 arbitrary extra qubits: any cycle subspace beyond
          {0, b}, and the eta-signature of every extra cycle found
          (decides the |b| = 6 rung m >= 3 EXACTLY);
        - pair-union + 1 extra qubit: same, for the |b| = 10 rung m >= 1.
  T4  weight-6 one-cycles: full enumeration (SAT), split by class type
      (stabilizer / im(Delta) logical / non-im(Delta) logical); support
      shapes (x-column histograms) and max overlap with any hexagon.
      Feeds the human-grade shape lemma behind the |b| = 6 rung.
  T5  ker(d2) explicit structure (the 6-dim 2-cycle space): weight profile,
      generators as polynomials.

Discovery/validation only; never load-bearing in a final analytic proof.
"""
from __future__ import annotations

from itertools import combinations

import numpy as np
from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195

from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.checks import bb_check_matrices
from bb_lab.linalg import nullspace_f2, rank_f2, quotient_complement_basis
from bb_lab.sat_distance import _xor_chain

Gb = ZmZn(6, 6)
Ab = Poly.from_string("x^3 + y + y^2", Gb)
Bb = Poly.from_string("y^3 + x + x^2", Gb)
cm_b = bb_check_matrices(Ab, Bb)
HXb, HZb = cm_b.H_X & 1, cm_b.H_Z & 1
nb = Gb.cardinality
n = 2 * nb
d2b = HZb.T

Gc = ZmZn(12, 6)
Ac = Poly.from_string("x^3 + y + y^2", Gc); Bc = Poly.from_string("y^3 + x + x^2", Gc)
cm_c = bb_check_matrices(Ac, Bc)
HZc = cm_c.H_Z & 1

def base_of(g): return (g[0] % 6, g[1])

# cut-0 d2c (for eta), as in the foundations script
def d2c_cut0():
    def sheet(g): return 1 if g[0] >= 6 else 0
    nc = Gc.cardinality
    row_perm = np.empty(nc, dtype=int); col_perm = np.empty(2 * nc, dtype=int)
    for g in Gc:
        gi, bi = Gc.index(g), Gb.index(base_of(g))
        row_perm[gi] = sheet(g) * nb + bi
        for blk in (0, 1):
            col_perm[blk * nc + gi] = sheet(g) * n + blk * nb + bi
    HZc_p = np.zeros_like(HZc); HZc_p[row_perm[:, None], col_perm[None, :]] = HZc
    return HZc_p[:nb, n:].T

d2c0 = d2c_cut0()
ker_d2b = nullspace_f2(d2b)
logXb = quotient_complement_basis(HXb, nullspace_f2(HZb))
imD_cls = (((d2c0 @ ker_d2b.T).T % 2) @ logXb.T) % 2
mu = nullspace_f2(imD_cls)
eta = (mu @ logXb) % 2

def class_type(c) -> str:
    cv = (logXb @ (c & 1)) % 2
    if not cv.any():
        return "stab"
    return "imD" if not ((eta @ (c & 1)) % 2).any() else "NON-imD"

# ------------------------------------------------------------------------ T1
print("=== T1: hexagon overlap autocorrelation ===")
cols = d2b.T                                     # 36 x 72, col g = supp(d2 delta_g)
ov_table = {}
for d in Gb:
    if d == (0, 0):
        continue
    g0 = Gb.index((0, 0)); g1 = Gb.index(d)
    ov = int((cols[g0] & cols[g1]).sum())
    if ov:
        ov_table[d] = ov
print(f"  max pairwise overlap = {max(ov_table.values())} (claim: 1)")
print(f"  D = {{delta : ov = 1}}, |D| = {len(ov_table)} (claim: 12)")
print(f"  D = {sorted(ov_table)}")
xdeg = sorted({d[0] for d in ov_table})
print(f"  x-degrees present in D: {xdeg}")
# symbolic cross-check: differences of A-monomials and of B-monomials
def diffs(mons):
    out = set()
    for m1 in mons:
        for m2 in mons:
            if m1 != m2:
                out.add(((m1[0] - m2[0]) % 6, (m1[1] - m2[1]) % 6))
    return out
A_mons = [(3, 0), (0, 1), (0, 2)]
B_mons = [(0, 3), (1, 0), (2, 0)]
dA, dB = diffs(A_mons), diffs(B_mons)
print(f"  symbolic: |dA| = {len(dA)} (x-deg {sorted({d[0] for d in dA})}), "
      f"|dB| = {len(dB)} (x-deg {sorted({d[0] for d in dB})}), disjoint: {not (dA & dB)}")
print(f"  D == dA u dB: {set(ov_table) == (dA | dB)}")

# ------------------------------------------------------------------------ T2
print("\n=== T2: overlap Cayley graph Cay(G, D) clique structure ===")
Dset = set(ov_table)
verts = list(Gb)
adj = {v: set() for v in verts}
for v in verts:
    for d in Dset:
        w = ((v[0] + d[0]) % 6, (v[1] + d[1]) % 6)
        adj[v].add(w)
tri = sum(1 for v in verts for w in adj[v] for u in adj[v] if w < u and u in adj[w]) // 1
tri_count = 0
for v in verts:
    for w in adj[v]:
        if w <= v: continue
        for u in adj[v] & adj[w]:
            if u > w:
                tri_count += 1
def max_clique():
    best = 2 if any(adj.values()) else 1
    order = verts
    def extend(clique, cand):
        nonlocal best
        if len(clique) > best:
            best = len(clique)
        for i, v in enumerate(cand):
            if len(clique) + len(cand) - i <= best:
                return
            extend(clique + [v], [w for w in cand[i+1:] if w in adj[v]])
    extend([], order)
    return best
print(f"  triangles: {tri_count}, max clique: {max_clique()}")

# ------------------------------------------------------------------------ T3
print("\n=== T3: local cycle spaces (the rung facts) ===")
hex0 = np.flatnonzero(cols[Gb.index((0, 0))])
r_hex = rank_f2(HXb[:, hex0])
print(f"  single hexagon: |supp| = {len(hex0)}, rank HXb|hex = {r_hex} "
      f"(cycle dim = {len(hex0) - r_hex}; claim 1)")

pair_ranks = {}
for d in sorted(Dset):
    un = np.flatnonzero(cols[Gb.index((0, 0))] | cols[Gb.index(d)])
    pair_ranks[d] = (len(un), rank_f2(HXb[:, un]))
print("  overlapping pairs (union, rank, cycle dim) per delta:")
for d, (sz, r) in pair_ranks.items():
    print(f"    delta {d}: |union| = {sz}, rank = {r}, cycle dim = {sz - r} (claim 2)")

# hexagon + 2 extra qubits: exact decision of the |b|=6 rung (m >= 3)
print("  hexagon + 2 extra qubits sweep (decides |b|=6 rung m >= 3):")
outside = [q for q in range(n) if q not in set(hex0)]
base_cyc = nullspace_f2(HXb[:, hex0])            # inside-hex cycle coords
extra_found = []
for q1, q2 in combinations(outside, 2):
    S = np.concatenate([hex0, [q1, q2]])
    sub = HXb[:, S]
    dim = len(S) - rank_f2(sub)
    if dim > 1:
        ks = nullspace_f2(sub)
        for kvec in ks:
            c = np.zeros(n, np.uint8); c[S] = kvec
            if c[q1] or c[q2]:                   # genuinely uses an extra qubit
                extra_found.append((q1, q2, class_type(c), int(c.sum())))
print(f"    pairs with extra cycles: {len(set((a, b) for a, b, *_ in extra_found))} "
      f"of {len(outside) * (len(outside) - 1) // 2}")
types = {}
for *_pair, t, w in extra_found:
    types.setdefault((t, w), 0)
    types[(t, w)] += 1
print(f"    extra-cycle (class, weight) histogram: {types}")
print(f"    any NON-imD extra cycle (would kill m>=3): "
      f"{any(t == 'NON-imD' for *_p, t, _w in extra_found)}")

# pair union + 1 extra qubit: the |b|=10 rung with one slack qubit
print("  pair union + 1 extra qubit sweep (|b|=10 rung, m >= 1 with margin):")
bad10 = 0
for d in sorted(Dset):
    un = np.flatnonzero(cols[Gb.index((0, 0))] | cols[Gb.index(d)])
    out2 = [q for q in range(n) if q not in set(un)]
    for q1 in out2:
        S = np.concatenate([un, [q1]])
        sub = HXb[:, S]
        dim = len(S) - rank_f2(sub)
        if dim > 2:
            ks = nullspace_f2(sub)
            for kvec in ks:
                c = np.zeros(n, np.uint8); c[S] = kvec
                if c[q1] and class_type(c) == "NON-imD":
                    bad10 += 1
print(f"    NON-imD cycles within pair-union + 1 qubit: {bad10}")

# ------------------------------------------------------------------------ T4
print("\n=== T4: all weight-6 one-cycles, by class type ===")
pool = IDPool(); cnf = CNF()
uv = [pool.id() for _ in range(n)]
for r in HXb:
    o = _xor_chain((uv[i] for i in np.flatnonzero(r)), pool, cnf)
    if o is not None:
        cnf.append([-o])
cnf.append(list(uv))                              # nonzero
card = CardEnc.atmost(lits=uv, bound=6, vpool=pool, encoding=EncType.seqcounter)
cnf.extend(card.clauses)
solver = Cadical195(bootstrap_with=cnf.clauses)
w6 = []
while solver.solve():
    model = set(l for l in solver.get_model() if l > 0)
    c = np.array([1 if q in model else 0 for q in uv], np.uint8)
    w6.append(c)
    solver.add_clause([-uv[i] if c[i] else uv[i] for i in range(n)])
    if len(w6) >= 5000:
        print("  !! cap hit"); break
solver.delete()
w6 = [c for c in w6 if c.sum() == 6]              # card encoder allows < 6 too; keep exact
hist = {}
for c in w6:
    hist.setdefault(class_type(c), []).append(c)
print(f"  weight-6 cycles: {sum(len(v) for v in hist.values())} total; "
      f"by type: {{k: len(v) for k, v in hist.items()}}".replace("'", ""))
for t, lst in sorted(hist.items()):
    print(f"  type {t}: {len(lst)}")
    # shape: x-column histogram (per block) and max hexagon overlap
    shapes = {}
    max_hex_ov = 0
    for c in lst:
        xs = []
        for q in np.flatnonzero(c):
            blk, gi = divmod(q, nb)
            xs.append(Gb[gi][0] if hasattr(Gb, "__getitem__") else list(Gb)[gi][0])
        ncols = len(set(xs))
        shapes.setdefault(ncols, 0); shapes[ncols] += 1
        for g in Gb:
            ovv = int((c & cols[Gb.index(g)]).sum())
            max_hex_ov = max(max_hex_ov, ovv)
    print(f"    distinct-x-column count histogram: {shapes}; "
          f"max overlap with any hexagon: {max_hex_ov}")

# ------------------------------------------------------------------------ T5
print("\n=== T5: ker(d2) structure ===")
print(f"  dim = {ker_d2b.shape[0]}")
wts = sorted(int(z.sum()) for z in ker_d2b)
print(f"  basis weights: {wts}")
min_w = min(int(((ker_d2b[np.array([bool((m >> i) & 1) for i in range(ker_d2b.shape[0])])]).sum(axis=0) % 2).sum())
            for m in range(1, 1 << ker_d2b.shape[0]))
print(f"  min nonzero 2-cycle weight: {min_w}")

# ------------------------------------------------------------------------ T6
print("\n=== T6: ingredients for the k <= 7 classification + rung locality ===")
# any two distinct qubits share at most one X-check (cross-correlation A.Bbar
# has 9 distinct terms; autocorrelations have 6 each, all multiplicity 1)
mx = 0
for i in range(n):
    for jq in range(i + 1, n):
        mx = max(mx, int((HXb[:, i] & HXb[:, jq]).sum()))
print(f"  max shared X-checks between two distinct qubits: {mx} (claim: 1)")
cross = {((a[0] - b[0]) % 6, (a[1] - b[1]) % 6) for a in A_mons for b in B_mons}
print(f"  A.Bbar distinct terms: {len(cross)} (claim: 9 -> shared-check bound)")
# octahedron-freeness of Cay(G, D): kills the k = 7 Turan-extremal K(3,2,2)
oct_count = 0
tris = [(a, b, c) for a in verts for b in adj[a] for c in (adj[a] & adj[b])]
for (a, b, c) in tris:
    for a2 in (adj[b] & adj[c]) - {a}:
        if a2 in adj[a]:
            continue
        for b2 in (adj[a] & adj[c] & adj[a2]) - {b}:
            if b2 in adj[b]:
                continue
            for c2 in (adj[a] & adj[b] & adj[a2] & adj[b2]) - {c}:
                if c2 not in adj[c]:
                    oct_count += 1
print(f"  ordered triangles in Cay(G,D): {len(tris)} (= 6 x 144)")
print(f"  octahedra K(2,2,2) in Cay(G,D): {oct_count} (claim: 0 -> no K(3,2,2), "
      f"k=7 Turan-extremal excluded)")

print("\nDone.")
