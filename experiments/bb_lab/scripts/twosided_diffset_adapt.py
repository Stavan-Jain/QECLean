"""Can the difference-set / two-sided technique (Theorem A two-sided splits)
be adapted to other polynomials?

The technique (proof secs (1,1),(1,3),(2,2)) depends ONLY on combinatorial
structure of A,B -- no F4/CRT engine:
  (D1) ov<=1   : difference sets dA, dB multiplicity-free  (=> |P.z| = 3|z|-2p+4T)
  (D2) disjoint : dA ∩ dB = empty                          (kills the (1,1) split)
  (D3) coord-sep: x(dA)∩x(dB)=∅  AND  y(dA)∩y(dB)=∅          (drives the projection
                  contradictions: one of pi_x(P)/pi_y(P) is a SPIKE, the other SPREAD)
  + 1-variable cyclic-code annihilator facts on the projections (frame-specific input).

We define PRED = (D1 ∧ D2 ∧ D3) and test, against SAT ground truth, whether
PRED implies the two-sided floor d2 >= 6 (= the technique's conclusion), on
SEVERAL group frames -- including frames with NO F4 structure (Z5xZ5, Z5xZ6)
to test frame-agnosticism.

d2(A,B) = min weight of a TWO-SIDED cycle: A.u_L = B.u_R, u_L!=0, u_R!=0.

CORRECTION (read this): this script sweeps the gross-SHAPE family
(A=x^a+y^b+y^c, B=y^d+x^e+x^f) only. On that family it finds D1&D2 already
sound (D3 rarely needed), which suggested D3 was dispensable. That conclusion
is WRONG in general: gross-shape excludes the Frobenius square A=B^2
((1+x+y)^2 = 1+x^2+y^2), which satisfies D1&D2 yet has a weight-(1+w) two-sided
cycle and VIOLATES D3. See `twosided_floor_counterexample.py` and
`frobenius_obstruction_verify.py`: the correct frame-agnostic criterion is
D1 & D2 & D3 (the `bb_lab.diffset_predicates` module packages it).
"""
from __future__ import annotations
import itertools, collections
import numpy as np

from bb_lab.group import AbelianGroup
from bb_lab.poly import Poly
from bb_lab.checks import bb_check_matrices, circulant
from bb_lab.linalg import rank_f2
from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195


def diffset(supp, G):
    """nonzero-difference multiset of a support (Counter over G), and the set."""
    c = collections.Counter()
    pts = list(supp)
    for g in pts:
        for h in pts:
            if g != h:
                c[G.sub(g, h)] += 1
    return c

def predicates(A: Poly, B: Poly, G):
    dA = diffset(A.support, G); dB = diffset(B.support, G)
    ovA = max(dA.values()) if dA else 0
    ovB = max(dB.values()) if dB else 0
    setA, setB = set(dA), set(dB)
    disj = setA.isdisjoint(setB)
    xA = {d[0] for d in setA}; xB = {d[0] for d in setB}
    yA = {d[1] for d in setA}; yB = {d[1] for d in setB}
    xsep = xA.isdisjoint(xB); ysep = yA.isdisjoint(yB)
    D1 = (ovA <= 1 and ovB <= 1)
    D2 = disj
    D3 = (xsep and ysep)
    return dict(ovA=ovA, ovB=ovB, D1=D1, D2=D2, D3=D3, PRED=(D1 and D2 and D3))

def min_twosided_cycle(HX, nL, cap=7):
    """min weight v in ker(HX) with v[:nL] != 0 AND v[nL:] != 0 (two-sided cycle)."""
    HX = (HX & 1).astype(np.uint8); rows, n = HX.shape
    for w in range(2, cap + 1):
        pool = IDPool(); vs = [pool.id() for _ in range(n)]; cnf = CNF()
        for r in range(rows):
            idx = np.flatnonzero(HX[r])
            if idx.size == 0: continue
            acc = vs[idx[0]]
            for i in idx[1:]:
                nw = pool.id(); x = vs[i]
                cnf.append([-nw,-acc,-x]); cnf.append([-nw,acc,x])
                cnf.append([nw,-acc,x]);  cnf.append([nw,acc,-x]); acc = nw
            cnf.append([-acc])
        cnf.append(list(vs[:nL]))     # left block nonzero
        cnf.append(list(vs[nL:]))     # right block nonzero
        if w < n:
            cnf.extend(CardEnc.atmost(lits=vs, bound=w, vpool=pool,
                                      encoding=EncType.seqcounter).clauses)
        s = Cadical195(bootstrap_with=cnf.clauses)
        try:
            if s.solve(): return w
        finally:
            s.delete()
    return cap + 1   # ">cap"


def gross_shapes(G):
    l, m = G.orders
    As = [Poly.from_support([(a,0),(0,b),(0,c)], G)
          for a in range(1,l) for b,c in itertools.combinations(range(1,m),2)]
    Bs = [Poly.from_support([(0,d),(e,0),(f,0)], G)
          for d in range(1,m) for e,f in itertools.combinations(range(1,l),2)]
    return As, Bs

def sweep_frame(orders, label, kpos_only=True, cap=None):
    G = AbelianGroup(orders); nL = G.cardinality
    As, Bs = gross_shapes(G)
    rows = []     # (d2, D1, D2, D3)
    for A in As:
        for B in Bs:
            ch = bb_check_matrices(A, B)
            k = ch.num_qubits - 2*rank_f2(ch.H_X)
            if kpos_only and k <= 0:
                continue
            pr = predicates(A, B, G)
            d2 = min_twosided_cycle(ch.H_X, nL)
            rows.append((d2, pr["D1"], pr["D2"], pr["D3"]))
            if cap and len(rows) >= cap:
                break
        if cap and len(rows) >= cap:
            break
    n = len(rows)
    print(f"\n### frame {label}  (n = {2*nL}) — {n} gross-shape codes with k>0")
    if n == 0:
        return rows
    n_lt6 = sum(1 for r in rows if r[0] < 6)
    print(f"   codes with d2 < 6 (light two-sided cycle exists): {n_lt6} / {n}")
    # candidate sufficient conditions -> is it sound (no d2<6 among holders)? how many does it cover?
    cands = {
        "D1 (ov<=1)":            lambda r: r[1],
        "D1 & D2 (+disjoint)":   lambda r: r[1] and r[2],
        "D1 & D3 (+coord-sep)":  lambda r: r[1] and r[3],
        "PRED (D1&D2&D3)":       lambda r: r[1] and r[2] and r[3],
    }
    print(f"   sufficiency test  [pred => d2>=6] :")
    print(f"      {'condition':22s} {'#holds':>7s} {'#hold&d2<6':>11s} {'sound?':>7s} {'covers d2>=6':>13s}")
    n_ge6 = n - n_lt6
    for name, f in cands.items():
        hold = [r for r in rows if f(r)]
        bad = sum(1 for r in hold if r[0] < 6)
        cover = sum(1 for r in hold if r[0] >= 6)
        sound = "YES" if bad == 0 else f"NO({bad})"
        cov = f"{cover}/{n_ge6}" if n_ge6 else "-"
        print(f"      {name:22s} {len(hold):7d} {bad:11d} {sound:>7s} {cov:>13s}")
    return rows


print("="*72)
print("Distilling the two-sided technique into checkable predicates, then")
print("testing PRED = (ov<=1 & disjoint-diffsets & coord-separated) => d2>=6")
print("across frames (incl. NON-F4 frames Z5xZ5, Z5xZ6).")
print("="*72)

# anchor: gross base predicates + d2
G66 = AbelianGroup((6,6))
gA = Poly.from_string("x^3 + y + y^2", G66); gB = Poly.from_string("y^3 + x + x^2", G66)
chg = bb_check_matrices(gA, gB)
print("\nANCHOR gross base [[72,12,6]]:")
print("   predicates:", predicates(gA, gB, G66))
print("   d2 (two-sided cycle floor) =", min_twosided_cycle(chg.H_X, 36),
      "   (technique claims >=6)")

# the [[36,4,4]] base (its distance was two-sided = 4)
G36 = AbelianGroup((3,6))
aA = Poly.from_string("x^2 + y + y^3", G36); aB = Poly.from_string("1 + x + y^2", G36)
cha = bb_check_matrices(aA, aB)
print("\nANCHOR [[36,4,4]] base (distance is two-sided, d=4):")
print("   predicates:", predicates(aA, aB, G36))
print("   d2 =", min_twosided_cycle(cha.H_X, 18))

# sweeps
# bb_108 anchor: a REAL d=10 code on Z9xZ6 (Z9 -> F64 frame; engine undefined there)
G96 = AbelianGroup((9,6))
bA = Poly.from_string("x^3 + y + y^2", G96); bB = Poly.from_string("y^3 + x + x^2", G96)
ch108 = bb_check_matrices(bA, bB)
print("\nANCHOR bb_108 [[108,8,10]] on Z9xZ6 (F64 frame — engine does NOT apply):")
print("   predicates:", predicates(bA, bB, G96))
print("   d2 =", min_twosided_cycle(ch108.H_X, 54), " (actual code d = 10)")

sweep_frame((6,6), "Z6xZ6  (F4 engine frame)")
sweep_frame((7,7), "Z7xZ7  (F8 frame, NO engine)")
sweep_frame((9,6), "Z9xZ6  (F64 frame, NO engine; bb_108 lives here)", cap=120)
print("\nDONE")
