# Counterexample-hunt brief (A11 Entry 2b residue)

Work in /Users/stavanjain/Code/QuantumErrorCorrectionLean-fresh/.claude/worktrees/gallant-greider-66ad94/experiments/bb_lab
(run Python as `uv run python ...` from that dir; no `lake`; nothing outside experiments/bb_lab; ~60-90 min compute; commit nothing).

READ FIRST: notes/A11_literal_lift_criterion.md (Entries 2, 2b) and scripts/a11_s4_dangerous_reduction.py.

GOAL: find a counterexample to "C-safe implies doubling" for literal axis lifts of BB codes:
an instance (H = Z_ell x Z_m, A, B, axis) where C-safe HOLDS but d(cover) < 2*d(base).

C-safe for a cell = (1) k(cover) = k(base) [code_params(...).k]; (2) tight witness [profile_pair in
scripts/a9_lean_target_screen.py]; (3) safe floor: safefloor_verdict(A, B, axis, Gb, cap=2d-1, tag)
in scripts/a11_s3_diagnose.py returns True.

Building blocks: Poly.from_string / AbelianGroup((ell,m)) [bb_lab.poly, bb_lab.group];
bb_check_matrices [bb_lab.checks]; cover_group + lift_poly [scripts/a9_lean_target_screen.py];
exact distances via x_distance(checks, weight_upper_bound=W) [bb_lab.sat_distance].

ALREADY SCREENED, zero violations (skip): all weight-3 pairs on Z3xZ3/Z3xZ4/Z3xZ5/Z3xZ6/Z4xZ6
both axes; Z6xZ6 anchorable classes; 13 hard-negative orbits.

STRATEGY, priority order:
S1 weight-4/weight-5 (A,B) random samples (2000-5000/frame after k>0 rank filter; d(base)>=2 by SAT)
   on Z3xZ3..Z4xZ6 + Z4xZ4, Z5xZ5, Z3xZ7, Z4xZ5, Z5xZ6; fail-fast C-safe (k, witness, safe floor);
   every C-safe-true cell: compute d(cover) with weight_upper_bound=2*d(base). d(cover) < 2d = jackpot.
   LOG every C-safe-true cell + its d(cover).
S2 targeted concentration search: light stabilizers b (H_Z rows, 2-row sums, translates, |b| < 2d);
   minimal-seam preimage y_b (solve d2 y = b over F2, reduce |h|+|h'| over ker d2 coset);
   Sigma-punctured coset min (adapt coset_min_le in a11_s3_diagnose.py: cardinality restricted to
   complement of Sigma = supp(h) u supp(h')). Punctured min < d - |b|/2 on a C-safe instance =
   near-violation -> check d(cover) exactly.
S3 adversarial: spread both polynomials across the doubled axis to fatten seams; k>0, d(base)>=2.

VALIDATION (mandatory): sanity-ladder every new SAT encoding on controls first —
Z3Z6 pair (A="x^2 + y + y^3", B="1 + x + y^2", axis x): d_base=4, d_cover=8, safe minima >=8;
hit3-stored (Z6xZ6, A="y^3 + x + x^2", B="y + x*y^2 + x^2", axis x): safe histogram {6:12, 8:45, >=12:6}.
x_distance witnesses are X-type (ker H_Z, not ker H_X) — sector logic uses the dual complex.
Any counterexample: STOP, re-verify from scratch in pure numpy (k/d both levels, per-class floor,
extract + verify the light cover logical), make it the centerpiece.

DELIVERABLES: scripts/a11_cx_*.py; data/a11/cx/*.jsonl (append, resumable);
data/a11/cx/REPORT.md (coverage table frames x weights, C-safe-true counts, violations,
near-miss margins, verdict). FINAL MESSAGE must be self-contained: verdict + coverage +
sharpest near-miss + paths + surprises.
