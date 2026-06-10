"""A1 gap-closer: verify the gross-chain steps are SRB-class covers.

For each step (cover -> base) of the chain
  [[144,12,12]] (Z12xZ6, A=x^3+y+y^2, B=y^3+x+x^2)
  -> [[72,12,6]]  (Z6xZ6,  same A,B)
  -> [[36,8,4]]   (Z3xZ6,  A'=1+y+y^2, B'=y^3+x+x^2)
  -> [[18,8,2]]   (Z3xZ3,  A''=1+y+y^2, B''=1+x+x^2)

check, via bb_lab.homological_bounds.enumerate_base_codes (which implements
the SRB Theorem 3.1 mod-(l',m') projection on monomial exponents):

  1. the stated base appears among the enumerated bases of the cover,
     with the exact stated polynomials;
  2. h = 2 (and therefore is_rigorous == False, h even);
  3. monomial-count preservation (weight(A_proj) == weight(A_cover)):
     SRB Thm 3.1 needs a monomial-by-monomial congruence, so a projection
     with F2-cancellation would NOT be an SRB-class cover even though the
     lab's projection map tolerates it;
  4. k at each level via code_params(bb_check_matrices(...)).
"""

from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.checks import bb_check_matrices, assert_css_commutation
from bb_lab.codeparams import code_params
from bb_lab.homological_bounds import enumerate_base_codes


def poly_str(p: Poly) -> str:
    def mono(g):
        parts = []
        for var, e in zip("xy", g):
            if e == 1:
                parts.append(var)
            elif e > 1:
                parts.append(f"{var}^{e}")
        return "*".join(parts) if parts else "1"
    return " + ".join(mono(g) for g in sorted(p.support)) or "0"


CHAIN = [
    ("[[144,12,12]] gross", "x^3 + y + y^2", "y^3 + x + x^2", (12, 6)),
    ("[[72,12,6]]",         "x^3 + y + y^2", "y^3 + x + x^2", (6, 6)),
    ("[[36,8,4]]",          "1 + y + y^2",   "y^3 + x + x^2", (3, 6)),
    ("[[18,8,2]]",          "1 + y + y^2",   "1 + x + x^2",   (3, 3)),
]

# ---- k at every level -------------------------------------------------
print("=== k at every level (computed from check matrices) ===")
level_k = {}
for name, a_s, b_s, (l, m) in CHAIN:
    G = ZmZn(l, m)
    A = Poly.from_string(a_s, G)
    B = Poly.from_string(b_s, G)
    cm = bb_check_matrices(A, B)
    assert_css_commutation(cm)
    params = code_params(cm)
    level_k[name] = params
    print(f"  {name:22s} G=Z{l}xZ{m}  A={a_s:14s} B={b_s:14s} -> n={params.n}, k={params.k}")

# ---- per-step SRB Thm 3.1 check ---------------------------------------
print("\n=== chain steps: SRB Theorem 3.1 projection check ===")
for (cname, ca, cb, (cl, cm_)), (bname, ba, bb_, (bl, bm)) in zip(CHAIN, CHAIN[1:]):
    Gc = ZmZn(cl, cm_)
    Gb = ZmZn(bl, bm)
    Ac = Poly.from_string(ca, Gc)
    Bc = Poly.from_string(cb, Gc)
    Ab_expected = Poly.from_string(ba, Gb)
    Bb_expected = Poly.from_string(bb_, Gb)

    bases = enumerate_base_codes(Ac, Bc, Gc)
    match = [bc for bc in bases if bc.G_base == Gb]
    assert len(match) == 1, f"expected exactly one base at {Gb.label()}, got {len(match)}"
    bc = match[0]

    polys_match = (bc.A_base == Ab_expected) and (bc.B_base == Bb_expected)
    # SRB 3.1 wants monomial-wise congruence: no F2 cancellation allowed.
    no_cancel = (bc.A_base.weight() == Ac.weight()) and (bc.B_base.weight() == Bc.weight())
    k_cover = level_k[cname].k
    k_base = level_k[bname].k

    print(f"\n  step: {cname} (Z{cl}xZ{cm_}) -> {bname} (Z{bl}xZ{bm})")
    print(f"    u={bc.u}, t={bc.t}, h={bc.h}   (h even -> SRB 'rigorous' flag: {bc.is_rigorous})")
    print(f"    projected A = {poly_str(bc.A_base)}   expected {ba}   match: {bc.A_base == Ab_expected}")
    print(f"    projected B = {poly_str(bc.B_base)}   expected {bb_}   match: {bc.B_base == Bb_expected}")
    print(f"    monomial-count preserved (no F2 cancellation): {no_cancel}")
    print(f"    k_cover={k_cover}, k_base={k_base}, k equal: {k_cover == k_base}")
    print(f"    SRB Thm 3.1 (cover conditions):        {'SATISFIED' if polys_match and no_cancel else 'FAILED'}")
    print(f"    SRB Thm 4.5/4.6 hypothesis (h odd):    {'holds' if bc.h % 2 == 1 else 'FAILS (h=2 even)'}")
    print(f"    SRB Thm 4.7 hypothesis (h odd & k_h=k): "
          f"{'holds' if (bc.h % 2 == 1 and k_cover == k_base) else 'FAILS'}"
          f"{' (h even)' if bc.h % 2 == 0 else ''}"
          f"{' (k_h != k)' if k_cover != k_base else ''}")

# ---- also: is [[18,8,2]] reachable from [[72,12,6]] directly (h=4)? ----
print("\n=== bonus: [[72,12,6]] direct projections (all divisor pairs) ===")
G72 = ZmZn(6, 6)
A72 = Poly.from_string("x^3 + y + y^2", G72)
B72 = Poly.from_string("y^3 + x + x^2", G72)
for bc in enumerate_base_codes(A72, B72, G72):
    cmx = bb_check_matrices(bc.A_base, bc.B_base)
    p = code_params(cmx)
    no_cancel = bc.A_base.weight() == 3 and bc.B_base.weight() == 3
    print(f"  base G={bc.G_base.label():8s} h={bc.h}  A'={poly_str(bc.A_base):18s} "
          f"B'={poly_str(bc.B_base):18s} n={p.n:3d} k={p.k:2d}  3.1-class(no-cancel): {no_cancel}")
