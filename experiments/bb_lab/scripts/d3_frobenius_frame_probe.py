"""Adversarial probe: can a Frobenius pair A=B^2 satisfy D1&D2&D3?
If yes on any frame, the CORRECTED conjecture (D1&D2&D3 => floor>=2w) is ALSO
false, since Frobenius gives a weight (1+w) < 2w cycle. Uses the committed module."""
import itertools
from bb_lab.group import AbelianGroup
from bb_lab.poly import Poly
from bb_lab.diffset_predicates import (is_sidon, difference_sets_disjoint,
    coordinate_separated, frobenius_square, is_frobenius_related)

frames=[(5,5),(6,6),(7,7),(8,8),(9,9),(9,6),(7,5),(11,11),(13,13),(11,7),(12,6),(15,15)]
total_found=0
for orders in frames:
    G=AbelianGroup(orders)
    rest=[g for g in G if g!=(0,0)]
    found=[]
    for two in itertools.combinations(rest,2):
        B=Poly.from_support([(0,0),*two],G)
        if not is_sidon(B): continue
        A=frobenius_square(B)
        if A.weight()!=3: continue
        if is_sidon(A) and difference_sets_disjoint(A,B) and coordinate_separated(A,B):
            found.append((sorted(B.support),sorted(A.support)))
    total_found+=len(found)
    flag = "  <-- D3 FAILS to exclude Frobenius!" if found else ""
    print(f"  Z{orders[0]}xZ{orders[1]}: weight-3 Frobenius pairs with D1&D2&D3 = {len(found)}{flag}")
    for f in found[:2]: print("        B,A=", f)
print(f"\nTOTAL across frames: {total_found}")
print("(0 => D3 robustly excludes the Frobenius square in these frames)")
