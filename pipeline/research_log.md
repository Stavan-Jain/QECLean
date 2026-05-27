# Research log

Index of moonshot attempts (novel-math research track). Each entry links to
`attempts/<name>/result.md`. **Failures are first-class outputs** — document
what was tried and why it didn't work.

## Format

```
- YYYY-MM-DD — <name> — <status: success | partial | failed> —
  <one-line summary>. [details](attempts/<name>/result.md)
```

## Entries

- 2026-05-27 — bb_distance_conjecture_family_d_v3_h2_minwt_formula — partial —
  Pinned down the (4/9)|G| empirical pattern from session 1 as a rigorous
  structural identity for weight-3 BB codes: when there exist linearly-
  independent Z_3-homomorphisms φ_A, φ_B: G → Z_3 with each sending one
  polynomial's support to {0,1,2} and the other's to a constant, the
  element 1[φ_A ≠ 2 AND φ_B ≠ 2] is in H_2 with weight (4/9)·|G|. Verified
  437/437 corpus instances, 0 violations. Conjectured generalization
  ((w-1)/w)²·|G| for weight w (untested for w ≥ 4). Implemented as Tier-1
  feature `bb_lab.h2_minwt_formula` with 14 tests. Not a distance bound
  (per §6m); a positive structural identity. [details](attempts/bb_distance_conjecture_family_d_v3_h2_minwt_formula/result.md)
