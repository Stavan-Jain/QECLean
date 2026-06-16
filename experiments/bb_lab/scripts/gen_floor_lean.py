"""Emit a self-contained Lean floorOK (slab-filtered two-phase) for one orbit rep,
to validate the engine returns `true` and measure native_decide time.

Encoding: ring element = 4 slot-values (F4 = 0..3) in allS order
(0,0),(1,0),(0,1),(1,1).  Cost tables: FADD(16), WT5(512), D3V(128).
floorOK: ∀ slab (p0,p3,p4)∈Γ0×Γ3×Γ4: slabMin≥12 ∨
         ∀ (m1,m2) support classes: relaxed≥12 ∨ ∀ fiber (p1,p2): exact≥12.
"""
from __future__ import annotations
import sys
from itertools import product
import numpy as np
from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.checks import bb_check_matrices
from bb_lab.linalg import nullspace_f2

Gb = ZmZn(6, 6)
Ab = Poly.from_string("x^3 + y + y^2", Gb)
Bb = Poly.from_string("y^3 + x + x^2", Gb)
d2b = (bb_check_matrices(Ab, Bb).H_Z & 1).T
nb = 36
A_steps = [(3, 0), (0, 1), (0, 2)]; B_steps = [(0, 3), (1, 0), (2, 0)]
def d2c_mat(j):
    d2c = np.zeros((72, nb), np.uint8)
    for g in Gb:
        c = Gb.index(g)
        for blk, steps in ((0, B_steps), (1, A_steps)):
            for (sx, sy) in steps:
                if ((g[0]-j) % 6)+sx >= 6:
                    d2c[blk*nb+Gb.index(((g[0]+sx) % 6, (g[1]+sy) % 6)), c] ^= 1
    return d2c
D2C0 = d2c_mat(0); ker2 = nullspace_f2(d2b)
def span(rows):
    out = []
    for m in range(1 << rows.shape[0]):
        v = np.zeros(rows.shape[1], np.uint8)
        for i in range(rows.shape[0]):
            if (m >> i) & 1: v ^= rows[i]
        out.append(v)
    return out
Z2all = [z for z in span(ker2) if z.any()]
F4 = np.zeros((4, 4), np.uint8)
for a in range(4):
    for b in range(4):
        a0, a1 = a & 1, a >> 1; b0, b1 = b & 1, b >> 1
        F4[a, b] = ((a0 & b0) ^ (a1 & b1)) | ((((a0 & b1) ^ (a1 & b0) ^ (a1 & b1)) << 1))
ADD = np.zeros((4, 4), np.uint8)
for a in range(4):
    for b in range(4): ADD[a, b] = a ^ b  # F4 add = bitwise xor on the 2-bit rep
OR5 = {0: (0, 0), 1: (0, 1), 2: (1, 0), 3: (1, 1), 4: (1, 2)}; WP = [1, 2, 3]
def ch(v, j):
    o = [0, 0, 0, 0]; c, d = OR5[j]
    for g in Gb:
        if v[Gb.index(g)]:
            s = (g[0] % 2) | ((g[1] % 2) << 1); o[s] ^= WP[(c*(g[0] % 3)+d*(g[1] % 3)) % 3]
    return tuple(o)
def rm(f, g):
    o = [0, 0, 0, 0]
    for s1 in range(4):
        if f[s1]:
            for s2 in range(4):
                if g[s2]: o[s1 ^ s2] ^= int(F4[f[s1], g[s2]])
    return tuple(o)
def xo(a, b): return tuple(x ^ y for x, y in zip(a, b))
d0 = np.eye(nb, dtype=np.uint8)[Gb.index((0, 0))]
AH = {j: ch((d2b[nb:, :] @ d0) % 2, j) for j in range(5)}
BH = {j: ch((d2b[:nb, :] @ d0) % 2, j) for j in range(5)}
AF4 = [tuple(t) for t in product(range(4), repeat=4)]
AF2 = [e for e in AF4 if all(c < 2 for c in e)]
def gamma(j):  # (oL-side = Bhat*t, oR-side = Ahat*t) — matches validated slab_filter
    dom = AF2 if j == 0 else AF4; out = {}
    for t in dom: out[(rm(BH[j], t), rm(AH[j], t))] = True
    return list(out)
G = {j: gamma(j) for j in range(5)}
# value<->weight bijection -> WT5[v0 + 2*(v1+4*(v2+4*(v3+4*v4)))]
WT5 = [0]*512
for fb in range(512):
    vv = []
    for j, (c, d) in OR5.items():
        acc = 0
        for t1 in range(3):
            for t2 in range(3):
                if (fb >> (3*t1+t2)) & 1: acc ^= WP[(c*t1+d*t2) % 3]
        vv.append(acc)
    v0, v1, v2, v3, v4 = vv
    WT5[v0 + 2*(v1+4*(v2+4*(v3+4*v4)))] = bin(fb).count("1")
# D3V[(v0*16+v3*4+v4)*4 + (a1+2a2)]
D3V = [99]*128
for v0 in range(2):
    for v3 in range(4):
        for v4 in range(4):
            for a1 in range(2):
                for a2 in range(2):
                    dom1 = (0,) if a1 == 0 else (1, 2, 3); dom2 = (0,) if a2 == 0 else (1, 2, 3)
                    D3V[(v0*16+v3*4+v4)*4+a1+2*a2] = min(
                        WT5[v0+2*(v1+4*(v2+4*(v3+4*v4)))] for v1 in dom1 for v2 in dom2)
def offs(w): return {j: (ch(w[:nb], j), ch(w[nb:], j)) for j in range(5)}
# orbits
def sw(z):
    o = np.zeros_like(z)
    for g in Gb: o[Gb.index((g[1], g[0]))] = z[Gb.index(g)]
    return o
def tr(z, dx, dy):
    o = np.zeros_like(z)
    for g in Gb: o[Gb.index(((g[0]+dx) % 6, (g[1]+dy) % 6))] = z[Gb.index(g)]
    return o
orbs = {}
for z in Z2all:
    cands = []
    for dx in range(6):
        for dy in range(6): cands.append(tr(z, dx, dy).tobytes()); cands.append(sw(tr(z, dx, dy)).tobytes())
    orbs.setdefault(min(cands), []).append(z)
KEYS = sorted(orbs, key=lambda k: (int(np.frombuffer(k, np.uint8).sum()), len(orbs[k])))

# pick orbit by CLI arg (default 4 = wt-24 with most live slabs)
oi = int(sys.argv[1]) if len(sys.argv) > 1 else 4
zrep = orbs[KEYS[oi]][0]; o = offs((D2C0 @ zrep) % 2); wt = int(zrep.sum())

def mask(e): return sum(1 << s for s in range(4) if e[s])
# fiber structure for comps 1,2: group by (maskL,maskR)
def fibers(j):
    d = {}
    for (vL, vR) in G[j]: d.setdefault((mask(vL), mask(vR)), []).append((vL, vR))
    classes = sorted(d)
    return classes, [d[c] for c in classes]
c1, f1 = fibers(1); c2, f2 = fibers(2)

def flat(pairs):  # list of (vL(4),vR(4)) -> flat [vL0..3, vR0..3, ...]
    out = []
    for (vL, vR) in pairs: out += list(vL) + list(vR)
    return out
def arr(name, xs): return f"def {name} : Array Nat := #[{','.join(map(str,xs))}]\n"

L = []
L.append("/- AUTO-GENERATED floorOK engine test (one orbit rep). -/\n")
L.append("set_option maxRecDepth 4096\n")
L.append(arr("ADD", [int(ADD[a, b]) for a in range(4) for b in range(4)]))
L.append(arr("WT5", WT5))
L.append(arr("D3V", D3V))
# offsets: oL[j*4+s], oR[j*4+s]
oL = [o[j][0][s] for j in range(5) for s in range(4)]
oR = [o[j][1][s] for j in range(5) for s in range(4)]
L.append(arr("oL", oL)); L.append(arr("oR", oR))
L.append(arr("G0", flat(G[0]))); L.append(arr("G3", flat(G[3]))); L.append(arr("G4", flat(G[4])))
# comps 1,2 fiber data: flat per class + offsets index
L.append(arr("F1", sum((flat(f) for f in f1), [])))
L.append(arr("F1off", np.cumsum([0]+[len(f) for f in f1]).tolist()))
L.append(arr("F1mL", [m[0] for m in c1])); L.append(arr("F1mR", [m[1] for m in c1]))
L.append(arr("F2", sum((flat(f) for f in f2), [])))
L.append(arr("F2off", np.cumsum([0]+[len(f) for f in f2]).tolist()))
L.append(arr("F2mL", [m[0] for m in c2])); L.append(arr("F2mR", [m[1] for m in c2]))
L.append(f"def nG0 : Nat := {len(G[0])}\ndef nG3 : Nat := {len(G[3])}\n"
         f"def nG4 : Nat := {len(G[4])}\ndef nC1 : Nat := {len(c1)}\ndef nC2 : Nat := {len(c2)}\n")

# the engine in Lean (Nat, tail-recursive)
L.append(r'''
@[inline] def gadd (a b : Nat) : Nat := ADD.getD (a*4+b) 0
@[inline] def wt5 (v0 v1 v2 v3 v4 : Nat) : Nat := WT5.getD (v0+2*(v1+4*(v2+4*(v3+4*v4)))) 99
@[inline] def d3 (v0 v3 v4 a1 a2 : Nat) : Nat := D3V.getD ((v0*16+v3*4+v4)*4+a1+2*a2) 99

-- pair value: array G, pair index k, slot s, side (0=L,1=R)
@[inline] def pv (G : Array Nat) (k s side : Nat) : Nat := G.getD (k*8+side*4+s) 0
@[inline] def ov (o : Array Nat) (j s : Nat) : Nat := o.getD (j*4+s) 0

-- exact cost of one (block,slot) cell given the five comp values already faded
-- slabMin contribution: min over a1,a2 of d3 at this (block,slot) for comps0,3,4
@[inline] def cellMin (v0 v3 v4 : Nat) : Nat :=
  min (min (d3 v0 v3 v4 0 0) (d3 v0 v3 v4 1 0)) (min (d3 v0 v3 v4 0 1) (d3 v0 v3 v4 1 1))

-- slab-min over all 8 (block,slot): comps 0,3,4 from p0,p3,p4 at indices a0,a3,a4
@[inline] def slabMin (a0 a3 a4 : Nat) : Nat :=
  (List.range 4).foldl (fun acc s =>
    acc + cellMin (gadd (ov oL 0 s) (pv G0 a0 s 0)) (gadd (ov oL 3 s) (pv G3 a3 s 0))
                  (gadd (ov oL 4 s) (pv G4 a4 s 0))
        + cellMin (gadd (ov oR 0 s) (pv G0 a0 s 1)) (gadd (ov oR 3 s) (pv G3 a3 s 1))
                  (gadd (ov oR 4 s) (pv G4 a4 s 1))) 0

-- relaxed cost: comps0,3,4 exact, comps1,2 by support mask m1,m2 (per block)
@[inline] def relaxed (a0 a3 a4 m1L m1R m2L m2R : Nat) : Nat :=
  (List.range 4).foldl (fun acc s =>
    acc + d3 (gadd (ov oL 0 s) (pv G0 a0 s 0)) (gadd (ov oL 3 s) (pv G3 a3 s 0))
             (gadd (ov oL 4 s) (pv G4 a4 s 0)) ((m1L >>> s) &&& 1) ((m2L >>> s) &&& 1)
        + d3 (gadd (ov oR 0 s) (pv G0 a0 s 1)) (gadd (ov oR 3 s) (pv G3 a3 s 1))
             (gadd (ov oR 4 s) (pv G4 a4 s 1)) ((m1R >>> s) &&& 1) ((m2R >>> s) &&& 1)) 0

-- exact cost over all five comps at pair indices a0,a1,a2,a3,a4 (G1,G2 via fiber arrays)
@[inline] def exCost (a0 a3 a4 : Nat) (p1 : Array Nat) (k1 : Nat) (p2 : Array Nat) (k2 : Nat) : Nat :=
  (List.range 4).foldl (fun acc s =>
    acc + wt5 (gadd (ov oL 0 s) (pv G0 a0 s 0)) (gadd (ov oL 1 s) (pv p1 k1 s 0))
              (gadd (ov oL 2 s) (pv p2 k2 s 0)) (gadd (ov oL 3 s) (pv G3 a3 s 0))
              (gadd (ov oL 4 s) (pv G4 a4 s 0))
        + wt5 (gadd (ov oR 0 s) (pv G0 a0 s 1)) (gadd (ov oR 1 s) (pv p1 k1 s 1))
              (gadd (ov oR 2 s) (pv p2 k2 s 1)) (gadd (ov oR 3 s) (pv G3 a3 s 1))
              (gadd (ov oR 4 s) (pv G4 a4 s 1))) 0

-- fiber check: ∀ p1 in F1 class i1, p2 in F2 class i2, exCost ≥ 12
def fiberOK (a0 a3 a4 i1 i2 : Nat) : Bool :=
  let lo1 := F1off.getD i1 0; let hi1 := F1off.getD (i1+1) 0
  let lo2 := F2off.getD i2 0; let hi2 := F2off.getD (i2+1) 0
  (List.range (hi1-lo1)).all (fun d1 =>
    (List.range (hi2-lo2)).all (fun d2 =>
      decide (12 ≤ exCost a0 a3 a4 F1 (lo1+d1) F2 (lo2+d2))))

-- two-phase over the support classes for a live slab
def liveOK (a0 a3 a4 : Nat) : Bool :=
  (List.range nC1).all (fun i1 =>
    (List.range nC2).all (fun i2 =>
      let rc := relaxed a0 a3 a4 (F1mL.getD i1 0) (F1mR.getD i1 0)
                                 (F2mL.getD i2 0) (F2mR.getD i2 0)
      (12 ≤ rc) || fiberOK a0 a3 a4 i1 i2))

-- floorOK: ∀ slab, slabMin ≥ 12 ∨ liveOK
def floorOK : Bool :=
  (List.range nG0).all (fun a0 =>
    (List.range nG3).all (fun a3 =>
      (List.range nG4).all (fun a4 =>
        (12 ≤ slabMin a0 a3 a4) || liveOK a0 a3 a4)))

theorem floor_holds : floorOK = true := by native_decide
''')
out = "".join(L)
path = sys.argv[2] if len(sys.argv) > 2 else "/tmp/floor_test.lean"
with open(path, "w") as fh: fh.write(out)
print(f"orbit oi={oi} wt={wt}; |G0|={len(G[0])} |G3|={len(G[3])} |G4|={len(G[4])} "
      f"nC1={len(c1)} nC2={len(c2)}; wrote {path} ({len(out)} bytes)")
