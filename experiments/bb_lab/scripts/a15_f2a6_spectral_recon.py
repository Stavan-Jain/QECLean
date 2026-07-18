"""A15 near-kernel classification, step 1: spectral structure of the
f2a6f17e base algebra F2[Z5 x Z15] and of the near-kernel specimens.

Facts to establish (numerically, exact GF(16) arithmetic):
  1. the semisimple decomposition: 20 components = GF(2) x GF(4) x GF(16)^18
     (2-cyclotomic orbits of the 75 characters);
  2. the zero sets of A-hat and B-hat: dim ker MA = dim ker MB = 4 forces
     each to vanish on exactly one GF(16) component; CHECK whether it is
     the SAME component S0 (this would make ker MA = ker MB = ker d2 and
     the transfer T = B-hat/A-hat well-defined and invertible off S0);
  3. the transfer profile T_i on every non-S0 component (orders, fixed
     points) — the object the light-boundary condition |u| + |T u| <= 14
     lives on;
  4. spectral support profiles of the near-kernel specimens (re-derived
     via the cutoff query): how many components carry u-hat — spectrally
     concentrated or spread?

GF(16) = F2[t]/(t^4 + t + 1), omega15 = t (order 15), omega5 = t^3.
Character (a, b) at group element (i, j): t^((3 a i + b j) mod 15).

Usage: uv run python scripts/a15_f2a6_spectral_recon.py
"""

from __future__ import annotations

import sys
from pathlib import Path

import numpy as np

LAB_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LAB_ROOT / "src"))

from bb_lab.group import AbelianGroup
from bb_lab.poly import Poly
from bb_lab.checks import circulant
from bb_lab.linalg import nullspace_f2, rank_f2

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195

A_STR, B_STR = "1 + y + x", "x*y^6 + x*y^10 + x^2*y^12"
ELL, M = 5, 15

Gb = AbelianGroup((ELL, M))
nb = Gb.cardinality
Ab, Bb = Poly.from_string(A_STR, Gb), Poly.from_string(B_STR, Gb)
MAb, MBb = circulant(Ab).astype(np.uint8), circulant(Bb).astype(np.uint8)
D2b = np.vstack([MAb, MBb]) % 2
elems_b = list(Gb)
base_idx = {g: i for i, g in enumerate(Gb)}

# ------------------------------------------------ GF(16) arithmetic (exact)
# elements 0..15 as bitmasks over basis 1, t, t^2, t^3; t^4 = t + 1
GF_MUL = np.zeros((16, 16), dtype=np.uint8)
def _mul(a: int, b: int) -> int:
    r = 0
    for k in range(4):
        if (b >> k) & 1:
            aa = a
            for _ in range(k):
                aa <<= 1
                if aa & 16:
                    aa ^= 0b10011  # t^4 = t + 1
            r ^= aa
    return r & 15
for a in range(16):
    for b in range(16):
        GF_MUL[a, b] = _mul(a, b)
GF_INV = np.zeros(16, dtype=np.uint8)
for a in range(1, 16):
    for b in range(1, 16):
        if GF_MUL[a, b] == 1:
            GF_INV[a] = b
# powers of t (order 15)
T_POW = np.zeros(15, dtype=np.uint8)
T_POW[0] = 1
for k in range(1, 15):
    T_POW[k] = GF_MUL[T_POW[k - 1], 2]  # t = bitmask 0b0010 = 2
assert T_POW.tolist().count(1) == 1 and GF_MUL[T_POW[14], 2] == 1

def gf_order(a: int) -> int:
    assert a != 0
    p, k = a, 1
    while p != 1:
        p = GF_MUL[p, a]
        k += 1
    return k

def char_eval(support: list[tuple[int, int]], a: int, b: int) -> int:
    """u-hat at character (a, b): sum over supp of t^((3ai + bj) mod 15)."""
    v = 0
    for (i, j) in support:
        v ^= T_POW[(3 * a * i + b * j) % 15]
    return v

# ------------------------------------------------ 1. orbits and components
chars = [(a, b) for a in range(5) for b in range(15)]
orbit_of: dict[tuple[int, int], int] = {}
orbits: list[list[tuple[int, int]]] = []
for c in chars:
    if c in orbit_of:
        continue
    o = []
    cur = c
    while cur not in orbit_of:
        orbit_of[cur] = len(orbits)
        o.append(cur)
        cur = ((2 * cur[0]) % 5, (2 * cur[1]) % 15)
    orbits.append(o)
sizes = sorted(len(o) for o in orbits)
print(f"components: {len(orbits)}, orbit sizes {sizes}")
assert sum(len(o) for o in orbits) == 75

# ------------------------------------------------ 2. zero sets of A, B
suppA = sorted(Ab.support)
suppB = sorted(Bb.support)
zero_A = set()
zero_B = set()
for oi, o in enumerate(orbits):
    a0, b0 = o[0]
    va = char_eval(suppA, a0, b0)
    vb = char_eval(suppB, a0, b0)
    if va == 0:
        zero_A.add(oi)
    if vb == 0:
        zero_B.add(oi)
print(f"A-hat vanishes on orbits {sorted(zero_A)} "
      f"(sizes {[len(orbits[i]) for i in sorted(zero_A)]})")
print(f"B-hat vanishes on orbits {sorted(zero_B)} "
      f"(sizes {[len(orbits[i]) for i in sorted(zero_B)]})")
same = zero_A == zero_B and len(zero_A) == 1
print(f"SAME single component S0: {same}")
S0 = next(iter(zero_A)) if len(zero_A) == 1 else None
# cross-check with F2 kernels
kerA = nullspace_f2(MAb)
kerB = nullspace_f2(MBb)
stack = np.vstack([kerA, kerB]) % 2
print(f"dim ker MA = {kerA.shape[0]}, dim ker MB = {kerB.shape[0]}, "
      f"rank of union = {rank_f2(stack)} (equal kernels iff = 4)")

# ------------------------------------------------ 3. transfer profile
print("\ntransfer T = B-hat / A-hat per component (orbit rep, value, order):")
for oi, o in enumerate(orbits):
    if oi == S0:
        print(f"  orbit {oi:2d} rep {o[0]}: S0 (A = B = 0)")
        continue
    a0, b0 = o[0]
    va, vb = char_eval(suppA, a0, b0), char_eval(suppB, a0, b0)
    if va == 0 or vb == 0:
        print(f"  orbit {oi:2d} rep {o[0]}: A={va} B={vb}  *** partial zero ***")
        continue
    tv = GF_MUL[vb, GF_INV[va]]
    print(f"  orbit {oi:2d} rep {o[0]} size {len(o)}: T = {tv:2d} "
          f"(mult order {gf_order(tv)})")

# ------------------------------------------------ 4. near-kernel specimens
print("\n== near-kernel specimens (5 fresh models) ==")
pool = IDPool()
fvar = [pool.id(f"f{i}") for i in range(nb)]
bvar = [pool.id(f"b{j}") for j in range(2 * nb)]
cnf = CNF()
for j in range(2 * nb):
    ins = [fvar[i] for i in np.nonzero(D2b[j])[0]]
    lits = [bvar[j], *ins]
    for m in range(16):
        neg = [(-1) ** ((m >> k) & 1) for k in range(4)]
        if sum(1 for x_ in neg if x_ < 0) % 2 == 1:
            cnf.append([neg[k] * lits[k] for k in range(4)])
cnf.extend(CardEnc.atmost(lits=bvar, bound=14, vpool=pool,
                          encoding=EncType.seqcounter))
cnf.append(bvar)
kerb = nullspace_f2(D2b).astype(np.uint8)
ker_elems = []
for mask in range(16):
    z = np.zeros(nb, dtype=np.uint8)
    for i in range(4):
        if (mask >> i) & 1:
            z ^= kerb[i]
    ker_elems.append(z)
for z in ker_elems:
    lits = [(-fvar[i] if z[i] else fvar[i]) for i in range(nb)]
    cnf.extend(CardEnc.atleast(lits=lits, bound=5, vpool=pool,
                               encoding=EncType.seqcounter))

with Cadical195(bootstrap_with=cnf.clauses) as s:
    for round_ in range(5):
        if not s.solve():
            print("  (no more models)")
            break
        model = s.get_model()
        f = np.zeros(nb, dtype=np.uint8)
        for i in range(nb):
            if model[fvar[i] - 1] > 0:
                f[i] = 1
        u = (MAb @ f) % 2
        v = (MBb @ f) % 2
        supp_u = [elems_b[i] for i in np.nonzero(u)[0]]
        supp_v = [elems_b[i] for i in np.nonzero(v)[0]]
        # spectral profiles
        prof_u = [oi for oi, o in enumerate(orbits)
                  if char_eval(supp_u, o[0][0], o[0][1]) != 0]
        prof_v = [oi for oi, o in enumerate(orbits)
                  if char_eval(supp_v, o[0][0], o[0][1]) != 0]
        print(f"  model {round_}: |u|={int(u.sum())} |v|={int(v.sum())}")
        print(f"    u supp {supp_u}")
        print(f"    v supp {supp_v}")
        print(f"    u-hat on {len(prof_u)}/20 orbits, v-hat on {len(prof_v)}/20"
              f" (S0 = {S0}; S0 in u-profile: {S0 in prof_u})")
        # block this b
        bb = np.concatenate([u, v])
        s.add_clause([(-bvar[j] if bb[j] else bvar[j])
                      for j in range(2 * nb)])
