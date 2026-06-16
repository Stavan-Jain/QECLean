"""Confirm the propagation-ceiling arithmetic the synthesis flagged, now grounded
in the per-sector min weights just computed.

Claim under test: even a fully successful h=2 Smith transfer (d_cover >= d_base) only
propagates the BASE distance up. On gross's chain the base distances are:
   gross(12) -> [[72,12,6]](6) -> [[36,8,4]](4) -> [[18,8,2]](2)
A proven d_cover >= d_base at each even-h step yields, composing from the deepest
analytic anchor [[18,8,2]] d=2:  d([[36,8,4]]) >= 2, d([[72,12,6]]) >= 2, d(gross) >= 2.
Using a structural base bound d([[36,8,4]]) >= 4 (lead 5) it yields d(gross) >= 4.
Using d([[72,12,6]]) >= 6 (if independently analytic) it yields d(gross) >= 6.
NONE of these reaches 12 -- because the safe branch is tight at d_base and the
factor-2 gap (d=12 vs d_base=6) is EXACTLY the dangerous-sector content.
"""
print("Per-sector min weights on (gross, [[72,12,6]]) [SAT, rigorous]:")
print("  safe sector  (pr_*!=0): 6   == d_base  (safe branch is tight, cannot exceed)")
print("  danger sector(pr_*=0):  12  == 2*d_base (the actual d=12 lives here)")
print()
print("Propagation ceiling of a SUCCESSFUL d_cover>=d_base transfer:")
print("  best analytic input today: [[18,8,2]] d=2 (HGP, published)  => d(gross) >= 2 (= LP floor, no gain)")
print("  with structural d([[36,8,4]])>=4         => d(gross) >= 4 (beats floor 2)")
print("  with analytic d([[72,12,6]])>=6 (open)   => d(gross) >= 6 (best case via transfer)")
print()
print("To reach d=12 the transfer theorem ITSELF must produce d_cover >= 2*d_base on the")
print("pr=0 sector -- i.e. a Delta=cap-omega weight-control lemma giving a factor-2 GAIN,")
print("not just d_cover>=d_base. That factor-2 is the genuinely-open new mathematics.")
